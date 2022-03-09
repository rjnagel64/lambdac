{-# LANGUAGE StandaloneDeriving, DerivingVia, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Opt where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Int
import Data.Traversable (for)

import Control.Monad.Reader
import Control.Monad.Writer

import CPS (TermK(..), TmVar(..), CoVar(..), FunDef(..), ContDef(..), ValueK(..))

-- [Compiling with Continuations, Continued] mostly.
-- CPS transformation, Closure Conversion, hopefully C code generation.

-- TODO: Reread "Compiling with Continuations and LLVM" for ideas about C code
-- generation

-- TODO: Break this into separate files, one per phase.
-- Honestly, the other files in src/ might deserve a separate repository.

-- TODO: Too many/Not enough sorts of variables. Be more consistent.

-- TODO: Attach a parser and driver
-- TODO: A simple type-checker.



-- TODO: Figure out call-pattern specialization
-- contify is basically call-pattern specialization for continuation arguments?
-- TODO: Implement Call Arity to be smarter about passing multiple arguments
-- together.

newtype InlineM a = InlineM { runInlineM :: Reader InlineEnv a }

-- GND is less verbose, at least.
deriving newtype instance Functor InlineM
deriving newtype instance Applicative InlineM
deriving newtype instance Monad InlineM
deriving newtype instance MonadReader InlineEnv InlineM

data InlineEnv
  = InlineEnv {
  -- | Functions and continuations larger than the threshold will not be
  -- inlined.
  -- TODO: different threshold for fun/cont?
    inlineSizeThreshold :: Int

  -- | If a continuation variable has an unfolding, it is stored here.
  , inlineCoDefs :: Map CoVar ContDef
  -- | If a function has an unfolding, it is stored here.
  , inlineFnDefs :: Map TmVar FunDef

  -- | Values are bound here, so that beta-redexes can reduce.
  , inlineValDefs :: Map TmVar ValueK

  -- | A substitution on term variables, used when beta-reducing and unfolding.
  , inlineTmSub :: Map TmVar TmVar
  -- | A substitution on term variables, used when beta-reducing and unfolding.
  , inlineCoSub :: Map CoVar CoVar
  }

withTmSub :: (TmVar, TmVar) -> InlineM a -> InlineM a
withTmSub (x, y) m = local f m
  where
    f env = env { inlineTmSub = Map.insert x y (inlineTmSub env) }

withCoSub :: (CoVar, CoVar) -> InlineM a -> InlineM a
withCoSub (x, y) m = local f m
  where
    f env = env { inlineCoSub = Map.insert x y (inlineCoSub env) }

withVal :: TmVar -> ValueK -> InlineM a -> InlineM a
withVal x v m = local f m
  where
    f env = env { inlineValDefs = Map.insert x v (inlineValDefs env) }

withFn :: FunDef -> InlineM a -> InlineM a
withFn fn@(FunDef f _ _ _ _ _) m = local g m
  where
    g env = env { inlineFnDefs = Map.insert f fn (inlineFnDefs env) }

withCont :: ContDef -> InlineM a -> InlineM a
withCont kont@(ContDef k _ _) m = local g m
  where
    g env = env { inlineCoDefs = Map.insert k kont (inlineCoDefs env) }

appTmSub :: TmVar -> InlineM TmVar
appTmSub x = do
  env <- ask
  case Map.lookup x (inlineTmSub env) of
    Nothing -> pure x
    Just y -> pure y

appCoSub :: CoVar -> InlineM CoVar
appCoSub k = do
  env <- ask
  case Map.lookup k (inlineCoSub env) of
    Nothing -> pure k
    Just k' -> pure k'

-- | Inline definitions and simplify redexes.
inlineK :: TermK -> InlineM TermK
-- Occurrences get inlined if their definition is in the environment.
-- (TODO: Inline decision based on context of occurrence, not just context of
-- definition?)
inlineK (JumpK k xs) = do
  env <- ask
  case Map.lookup k (inlineCoDefs env) of
    Nothing -> pure (JumpK k xs)
    Just (ContDef _ [(y, _)] e) -> withTmSub (y, xs !! 0) $ inlineK e
inlineK (CallK f x k) = do
  env <- ask
  case Map.lookup f (inlineFnDefs env) of
    Nothing -> pure (CallK f x k)
    Just (FunDef _ y _ k' _ e) -> withCoSub (k', k) $ withTmSub (y, x) $ inlineK e
-- Eliminators use 'inlineValDefs' to beta-reduce, if possible.
-- (A function parameter will not reduce, e.g.)
inlineK (CaseK x k1 s1 k2 s2) = do
  x' <- appTmSub x
  env <- ask
  case Map.lookup x' (inlineValDefs env) of
    Just (InlK y) -> inlineK (JumpK k1 [y])
    Just (InrK y) -> inlineK (JumpK k2 [y])
    Just _ -> error "case on non-inj value"
    Nothing -> pure (CaseK x' k1 s1 k2 s2)
inlineK (LetFstK x t y e) = do
  y' <- appTmSub y
  env <- ask
  -- We need to rebuild the LetFstK here because there still might be some
  -- variable that refers to it.
  -- TODO: Use usage information to discard dead bindings.
  case Map.lookup y' (inlineValDefs env) of
    Just (PairK p _) -> LetFstK x t y' <$> withTmSub (x, p) (inlineK e)
    Just _ -> error "fst on non-pair value"
    Nothing -> LetFstK x t y' <$> inlineK e
inlineK (LetSndK x t y e) = do
  y' <- appTmSub y
  env <- ask
  -- We need to rebuild the LetFstK here because there still might be some
  -- variable that refers to it.
  -- A DCE pass can remove it later.
  case Map.lookup y' (inlineValDefs env) of
    Just (PairK _ q) -> LetSndK x t y' <$> withTmSub (x, q) (inlineK e)
    Just _ -> error "snd on non-pair value"
    Nothing -> LetFstK x t y' <$> inlineK e
-- Functions and continuations are the things that need to be inlined.
-- These two cases decide whether or not a binding should be added to the environment.
-- When extending the environment:
-- * take a census (count how many occurrences of the bound variable, while
--   also reducing beta-redexes on the way)
-- * If 0 occurrences (after reduction), discard.
-- * If 1 occurrence, always inline
-- * If >1 occurrence, inline if small
--   (Or if would reduce? Maybe census collects argument patterns instead)
-- TODO: This is still incorrect if the binding is self-recursive.
-- TODO: Use loop-breakers to inline recursive bind groups.
inlineK (LetContK ks e) = case ks of
  [] -> inlineK e
  [k] -> LetContK ks <$> withCont k (inlineK e)
  _ -> LetContK ks <$> inlineK e
inlineK (LetFunK fs e) = case fs of
  [] -> inlineK e
  [f] -> LetFunK fs <$> withFn f (inlineK e)
  _ -> LetFunK fs <$> inlineK e
-- Value bindings are added to 'inlineValDefs', so they can be reduced.
inlineK (LetValK x t v e) = LetValK x t v <$> withVal x v (inlineK e)

-- Secrets of GHC Inliner:
-- data Usage = LoopBreaker | Dead | OnceSafe | MultiSafe | OnceUnsafe | MultiUnsafe
data Usage
  -- variable occurs zero times in body
  = Unused
  -- variable occurs up to once in all paths. (e.g., once on one path, never on the other)
  -- (Actually, does this make sense when considering case-continuations?)
  | AffineUsage
  -- variable occurs more than once
  | ManyUsage

-- | Count occurrences and pick loop breakers, annotating binders with usage
-- information.
-- TODO: Can't really return a map of usage information because it might shadow.
-- Need to annotate binders.
-- countOccurrences :: TermK -> (TermK, Map TmVar Usage, Map CoVar Usage)
-- countOccurrences e = (_, _, _)

-- TODO: Count occurrences of covariables as well.
-- countOccurrences :: Map TmVar ValueK -> Set TmVar -> TermK -> (TermK, Map TmVar Int)
-- If y in vs, that's an occurrence.
-- If y := (p, q) in env, substitute x := p, discard let x = fst y.
-- countOccurrences vs (LetFstK x y e) = _

-- Count number of 'let' bindings, recursively.
sizeK :: TermK -> Int
sizeK (LetFunK fs e) = sum (map (\ (FunDef f x _ k _ e') -> sizeK e') fs) + sizeK e
sizeK (LetValK x _ v e) = 1 + sizeK e


-- Higher-order functions can be eliminated using monomorphization
-- (I don't think I need this, because I can do closures+function pointers)


