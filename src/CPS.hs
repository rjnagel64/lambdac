{-# LANGUAGE StandaloneDeriving, DerivingVia, FlexibleInstances, MultiParamTypeClasses #-}

module CPS (TermK(..), TmVar(..), CoVar(..), FnName(..), FunDef(..), ContDef(..), ValueK(..)) where

import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.Reader

import qualified Source as S
import Source (Term(..), TmFun(..))

-- All sorts of variables exist in the same namespace.
newtype TmVar = TmVar String
  deriving (Eq, Ord)
newtype CoVar = CoVar String
  deriving (Eq, Ord)
newtype FnName = FnName String
  deriving (Eq, Ord)

-- | Terms in continuation-passing style.
--
-- CPS terms are basically (named, parametrized) basic blocks: a list of
-- assignments terminated by a control flow transfer.
--
-- TODO: Add type annotations to binders. (And maybe more general annotations?)
-- (Or more general annotations. I want to know how many occurrences there are
-- of each binder, for inlining and DCE.)
data TermK
  -- Assignments
  -- let val x = v in e
  = LetValK TmVar ValueK TermK
  -- let x = fst y in e
  | LetFstK TmVar TmVar TermK
  -- let x = snd y in e
  | LetSndK TmVar TmVar TermK
  -- let rec ks in e
  | LetContK [ContDef] TermK
  -- let rec fs in e
  | LetFunK [FunDef] TermK

  -- Block terminators
  -- k x, goto k(x)
  | JumpK CoVar TmVar
  -- f x k, call f(x, k)
  | CallK FnName TmVar CoVar
  -- case x of k1 | k2, branch
  | CaseK TmVar CoVar CoVar

-- | Named basic blocks
-- @k x := e@
data ContDef = ContDef CoVar TmVar TermK

-- | Function definitions
-- @f x k := e@
data FunDef = FunDef FnName TmVar CoVar TermK

-- | Values require no evaluation.
data ValueK
  = NilK
  | PairK TmVar TmVar
  | InlK TmVar
  | InrK TmVar

data TypeK
  -- unit
  = UnitK
  -- σ × τ
  | ProdK TypeK TypeK
  -- σ + τ
  | SumK TypeK TypeK
  -- σ -> τ
  -- Application requires argument variable of type σ, continuation variable of
  -- type τ.
  | ArrK TypeK TypeK


var :: S.TmVar -> TmVar
var (S.TmVar x) = TmVar x

-- | CPS-convert a term.
--
-- TODO: Complete these
-- TODO: Find a way to reduce the nesting.
-- ContT r m a = (a -> m r) -> m r
-- Term -> ContT TermK FreshM TmVar
-- The real question is, does it behave properly.
cps :: Term -> (TmVar -> FreshM TermK) -> FreshM TermK
cps (TmVarOcc x) k = k (var x)
cps (TmLam x e) k =
  freshTm "f" $ \ (TmVar f) ->
    freshCo "k" $ \k' ->
      let mkFun e' = [FunDef (FnName f) (var x) k' e'] in
      LetFunK <$> (mkFun <$> cpsTail e k') <*> k (TmVar f)
cps (TmRecFun fs e) k = do
  LetFunK <$> traverse cpsFun fs <*> cps e k
cps (TmApp e1 e2) k =
  cps e1 $ \ (TmVar v1) ->
    cps e2 $ \v2 ->
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          e <- k xv
          pure $ LetContK [ContDef kv xv e] (CallK (FnName v1) v2 kv)
cps (TmInl e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      LetValK x (InlK z) <$> k x
cps (TmInr e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      LetValK x (InrK z) <$> k x
cps (TmCase e xl el xr er) k =
  cps e $ \z ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            el' <- cpsTail el j
            er' <- cpsTail er j
            e' <- k x
            pure $
              LetContK [ContDef j x e'] $
                LetContK [ContDef k1 (var xl) el'] $
                  LetContK [ContDef k2 (var xr) er'] $
                    CaseK z k1 k2
cps (TmPair e1 e2) k =
  cps e1 $ \v1 ->
    cps e2 $ \v2 ->
      freshTm "x" $ \x ->
        LetValK x (PairK v1 v2) <$> k x
cps (TmFst e) k =
  cps e $ \v ->
    freshTm "x" $ \x ->
      LetFstK x v <$> k x
cps TmNil k =
  freshTm "x" $ \x -> LetValK x NilK <$> k x
cps (TmLet x e1 e2) k = do
  e2' <- cps e2 k
  freshCo "j" $ \j ->
    LetContK [ContDef j (var x) e2'] <$> cpsTail e1 j

cpsFun :: TmFun -> FreshM FunDef
cpsFun (TmFun f x e) = freshCo "k" $ \k -> FunDef (fnName f) (var x) k <$> cpsTail e k
  where
    fnName (S.TmVar x) = FnName x

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Term -> CoVar -> FreshM TermK
cpsTail (TmVarOcc x) k = pure (JumpK k (var x))
cpsTail (TmInl e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetValK x (InlK z) (JumpK k x))
cpsTail (TmPair e1 e2) k =
  cps e1 $ \x1 ->
    cps e2 $ \x2 ->
      freshTm "x" $ \x ->
        pure (LetValK x (PairK x1 x2) (JumpK k x))

newtype FreshM a = FreshM { runFreshM :: Reader (Map String Int) a }

deriving via Reader (Map String Int) instance Functor FreshM
deriving via Reader (Map String Int) instance Applicative FreshM
deriving via Reader (Map String Int) instance Monad FreshM
deriving via Reader (Map String Int) instance MonadReader (Map String Int) FreshM

freshTm :: String -> (TmVar -> FreshM a) -> FreshM a
freshTm x k = do
  scope <- ask
  case Map.lookup x scope of
    Nothing -> local (Map.insert x 0) (k (TmVar (x ++ "0")))
    Just i -> local (Map.insert x (i+1)) (k (TmVar (x ++ show i)))

freshCo :: String -> (CoVar -> FreshM a) -> FreshM a
freshCo x k = do
  scope <- ask
  case Map.lookup x scope of
    Nothing -> local (Map.insert x 0) (k (CoVar (x ++ "0")))
    Just i -> local (Map.insert x (i+1)) (k (CoVar (x ++ show i)))

runFresh :: FreshM a -> a
runFresh = flip runReader Map.empty . runFreshM

