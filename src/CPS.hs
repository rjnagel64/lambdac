{-# LANGUAGE StandaloneDeriving, DerivingVia, FlexibleInstances, MultiParamTypeClasses #-}

module CPS
    ( TermK(..)
    , TmVar(..)
    , CoVar(..)
    , FnName(..)
    , FunDef(..)
    , ContDef(..)
    , ArithK(..)
    , ValueK(..)

    , TypeK(..)

    , cpsMain
    , pprintTerm
    ) where

import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.Reader

import qualified Source as S
import Source (Term(..), TmFun(..))

-- call/cc: pass function return continuation to argument?
-- what if call/cc in contdef? in let-binding?
--
-- Maybe
--   fun callcc f k = f k k;
-- ?
-- I think that's the CPS representation, but I don't know how the source-level
-- version or the CPS translation works.
--
-- Typing rule for call/cc is Pierce's Law or something?
--
-- CPS transform for shift/reset?
-- Actually, not really. call/cc and control effects cause computational impurity,
-- which I don't want to deal with right now. Even if 'reset' can be used to
-- encapsulate the impurity.


-- All sorts of variables exist in the same namespace.
-- TODO: TmVar and FnName should be merged. Functions are values, so they
-- should use the same variable sort.
newtype TmVar = TmVar String
  deriving (Eq, Ord)
newtype CoVar = CoVar String
  deriving (Eq, Ord)
newtype FnName = FnName String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x) = x
instance Show CoVar where
  show (CoVar k) = k
instance Show FnName where
  show (FnName f) = f

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
  -- let x = iszero y in e
  | LetIsZeroK TmVar TmVar TermK
  -- let z = x + y in e
  | LetArithK TmVar ArithK TermK

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
  -- halt x
  | HaltK TmVar

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
  | IntK Int

data ArithK
  = AddK TmVar TmVar
  | SubK TmVar TmVar
  | MulK TmVar TmVar

data TypeK
  -- unit
  = UnitK
  -- σ × τ
  | ProdK TypeK TypeK
  -- σ + τ
  | SumK TypeK TypeK
  -- σ -> 0
  | ContK TypeK


var :: S.TmVar -> TmVar
var (S.TmVar x) = TmVar x

-- | CPS-convert a term.
--
-- TODO: Find a way to reduce the nesting.
-- ContT r m a = (a -> m r) -> m r
-- Term -> ContT TermK FreshM TmVar
-- The real question is, does it behave properly.
-- cps :: Map S.TmVar TypeK -> Term -> (TmVar -> TypeK -> FreshM TermK) -> FreshM TermK
cps :: Term -> (TmVar -> FreshM TermK) -> FreshM TermK
cps (TmVarOcc x) k = k (var x)
cps (TmLam x t e) k =
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
cps (TmInl a b e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      LetValK x (InlK z) <$> k x
cps (TmInr a b e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      LetValK x (InrK z) <$> k x
cps (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            el' <- cpsTail el j
            er' <- cpsTail er j
            e' <- k x
            pure $
              -- TODO: Case branches that accept multiple arguments at once
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
cps (TmSnd e) k =
  cps e $ \v ->
    freshTm "x" $ \x ->
      LetSndK x v <$> k x
cps TmNil k =
  freshTm "x" $ \x -> LetValK x NilK <$> k x
cps (TmInt i) k =
  freshTm "x" $ \x -> LetValK x (IntK i) <$> k x
cps (TmLet x t e1 e2) k = do
  e2' <- cps e2 k
  freshCo "j" $ \j ->
    LetContK [ContDef j (var x) e2'] <$> cpsTail e1 j
cps (TmAdd e1 e2) k =
  cps e1 $ \x ->
    cps e2 $ \y ->
      freshTm "z" $ \z ->
        LetArithK z (AddK x y) <$> k z
cps (TmSub e1 e2) k =
  cps e1 $ \x ->
    cps e2 $ \y ->
      freshTm "z" $ \z ->
        LetArithK z (SubK x y) <$> k z
cps (TmMul e1 e2) k =
  cps e1 $ \x ->
    cps e2 $ \y ->
      freshTm "z" $ \z ->
        LetArithK z (MulK x y) <$> k z
cps (TmIsZero e) k =
  cps e $ \v ->
    freshTm "x" $ \x ->
      LetIsZeroK x v <$> k x

cpsFun :: TmFun -> FreshM FunDef
cpsFun (TmFun f x t e) = freshCo "k" $ \k -> FunDef (fnName f) (var x) k <$> cpsTail e k
  where fnName (S.TmVar y) = FnName y

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Term -> CoVar -> FreshM TermK
cpsTail (TmVarOcc x) k = pure (JumpK k (var x))
cpsTail (TmLam x t e) k =
  freshTm "f" $ \ (TmVar f) ->
    freshCo "k" $ \k' ->
      let mkFun e' = [FunDef (FnName f) (var x) k' e'] in
      LetFunK <$> (mkFun <$> cpsTail e k') <*> pure (JumpK k (TmVar f))
cpsTail (TmLet x t e1 e2) k =
  -- let x = e1 in e2
  -- -->
  -- let j x = [[e2]] k in [[e1]] j
  freshCo "j" $ \j ->
    let mkCont e2' = [ContDef j (var x) e2'] in
    LetContK <$> (mkCont <$> cpsTail e2 k) <*> cpsTail e1 j
cpsTail (TmRecFun fs e) k = do
  LetFunK <$> traverse cpsFun fs <*> cpsTail e k
cpsTail (TmInl a b e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetValK x (InlK z) (JumpK k x))
cpsTail (TmInr a b e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetValK x (InrK z) (JumpK k x))
cpsTail (TmPair e1 e2) k =
  cps e1 $ \v1 ->
    cps e2 $ \v2 ->
      freshTm "x" $ \x ->
        pure (LetValK x (PairK v1 v2) (JumpK k x))
cpsTail (TmFst e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetFstK x z (JumpK k x))
cpsTail (TmSnd e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetSndK x z (JumpK k x))
cpsTail TmNil k =
  freshTm "x" $ \x ->
    pure (LetValK x NilK (JumpK k x))
cpsTail (TmInt i) k =
  freshTm "x" $ \x ->
    pure (LetValK x (IntK i) (JumpK k x))
cpsTail (TmAdd e1 e2) k =
  cps e1 $ \x ->
    cps e2 $ \y ->
      freshTm "z" $ \z ->
        pure (LetArithK z (AddK x y) (JumpK k z))
cpsTail (TmSub e1 e2) k =
  cps e1 $ \x ->
    cps e2 $ \y ->
      freshTm "z" $ \z ->
        pure (LetArithK z (SubK x y) (JumpK k z))
cpsTail (TmMul e1 e2) k =
  cps e1 $ \x ->
    cps e2 $ \y ->
      freshTm "z" $ \z ->
        pure (LetArithK z (MulK x y) (JumpK k z))
cpsTail (TmIsZero e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetIsZeroK x z (JumpK k x))
cpsTail (TmApp e1 e2) k =
  cps e1 $ \ (TmVar f) ->
    cps e2 $ \x ->
      pure (CallK (FnName f) x k)
cpsTail (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z ->
    freshCo "k1" $ \k1 ->
      freshCo "k2" $ \k2 -> do
        el' <- cpsTail el k
        er' <- cpsTail er k
        pure $
          -- TODO: Case branches that accept multiple arguments at once
          LetContK [ContDef k1 (var xl) el'] $
            LetContK [ContDef k2 (var xr) er'] $
              CaseK z k1 k2


cpsMain :: Term -> TermK
cpsMain e = runFresh $ cps e (\z -> pure (HaltK z))


newtype FreshM a = FreshM { runFreshM :: Reader (Map String Int) a }

deriving via Reader (Map String Int) instance Functor FreshM
deriving via Reader (Map String Int) instance Applicative FreshM
deriving via Reader (Map String Int) instance Monad FreshM
deriving via Reader (Map String Int) instance MonadReader (Map String Int) FreshM

freshTm :: String -> (TmVar -> FreshM a) -> FreshM a
freshTm x k = do
  scope <- ask
  case Map.lookup x scope of
    Nothing -> local (Map.insert x 1) (k (TmVar (x ++ "0")))
    Just i -> local (Map.insert x (i+1)) (k (TmVar (x ++ show i)))

freshCo :: String -> (CoVar -> FreshM a) -> FreshM a
freshCo x k = do
  scope <- ask
  case Map.lookup x scope of
    Nothing -> local (Map.insert x 1) (k (CoVar (x ++ "0")))
    Just i -> local (Map.insert x (i+1)) (k (CoVar (x ++ show i)))

runFresh :: FreshM a -> a
runFresh = flip runReader Map.empty . runFreshM


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermK -> String
pprintTerm n (HaltK x) = indent n $ "halt " ++ show x ++ ";\n"
pprintTerm n (JumpK k x) = indent n $ show k ++ " " ++ show x ++ ";\n"
pprintTerm n (CallK f x k) = indent n $ show f ++ " " ++ show x ++ " " ++ show k ++ ";\n"
pprintTerm n (CaseK x k1 k2) =
  indent n $ "case " ++ show x ++ " of " ++ show k1 ++ " | " ++ show k2 ++ ";\n"
pprintTerm n (LetValK x v e) =
  indent n ("let " ++ show x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFunK fs e) =
  indent n "letfun\n" ++ concatMap (pprintFunDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContK ks e) =
  indent n "letcont\n" ++ concatMap (pprintContDef (n+2)) ks ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetFstK x y e) =
  indent n ("let " ++ show x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndK x y e) =
  indent n ("let " ++ show x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetIsZeroK x y e) =
  indent n ("let " ++ show x ++ " = iszero " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetArithK x op e) =
  indent n ("let " ++ show x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e

pprintValue :: ValueK -> String
pprintValue NilK = "()"
pprintValue (PairK x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntK i) = show i
pprintValue (InlK x) = "inl " ++ show x
pprintValue (InrK y) = "inr " ++ show y

pprintArith :: ArithK -> String
pprintArith (AddK x y) = show x ++ " + " ++ show y
pprintArith (SubK x y) = show x ++ " - " ++ show y
pprintArith (MulK x y) = show x ++ " * " ++ show y

pprintFunDef :: Int -> FunDef -> String
pprintFunDef n (FunDef f x k e) =
  indent n (show f ++ " " ++ show x ++ " " ++ show k ++ " =\n") ++ pprintTerm (n+2) e

pprintContDef :: Int -> ContDef -> String
pprintContDef n (ContDef k x e) =
  indent n (show k ++ " " ++ show x ++ " =\n") ++ pprintTerm (n+2) e
