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
-- Continuation variables, meanwhile, truly are second-class (even if I forget
-- about that fact later on.)
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
-- @k (x:τ) := e@
data ContDef = ContDef CoVar TmVar TypeK TermK

-- | Function definitions
-- @f (x:τ) (k:σ) := e@
data FunDef = FunDef FnName TmVar TypeK CoVar TypeK TermK

-- | Values require no evaluation.
data ValueK
  = NilK
  | PairK TmVar TmVar
  | InlK TmVar
  | InrK TmVar
  | IntValK Int

data ArithK
  = AddK TmVar TmVar
  | SubK TmVar TmVar
  | MulK TmVar TmVar

data TypeK
  -- unit
  = UnitK
  -- int
  | IntK
  -- σ × τ
  | ProdK TypeK TypeK
  -- σ + τ
  | SumK TypeK TypeK
  -- σ -> 0
  | ContK TypeK

cpsType :: S.Type -> TypeK
cpsType S.TyUnit = UnitK
cpsType S.TyInt = IntK
cpsType (S.TySum a b) = SumK (cpsType a) (cpsType b)
cpsType (S.TyProd a b) = ProdK (cpsType a) (cpsType b)
cpsType (S.TyArr a b) = ContK (ProdK (cpsType a) (ContK (cpsType b)))
cpsType (S.TyVarOcc _) = error "not implemented: polymorphic cpsType"
cpsType (S.TyAll _ _) = error "not implemented: polymorphic cpsType"


var :: S.TmVar -> TmVar
var (S.TmVar x) = TmVar x

-- TODO: This actually has most elements of a type checker.
-- Maybe I should add Except and error-reporting?

-- | CPS-convert a term.
--
-- TODO: Find a way to reduce the nesting. ContT, maybe?
cps :: Map S.TmVar TypeK -> Term -> (TmVar -> TypeK -> FreshM (TermK, TypeK)) -> FreshM (TermK, TypeK)
cps env (TmVarOcc x) k = case Map.lookup x env of
  Nothing -> error "variable not in scope"
  Just t -> k (var x) t
cps env (TmLam x t e) k =
  freshTm "f" $ \ (TmVar f) ->
    freshCo "k" $ \k' -> do
      let t' = cpsType t
      (e', s') <- cpsTail (Map.insert x t' env) e k'
      let fs = [FunDef (FnName f) (var x) t' k' s' e']
      (e'', _t'') <- k (TmVar f) (ContK (ProdK t' (ContK s')))
      let res = LetFunK fs e''
      pure (res, ContK (ProdK t' (ContK s')))
cps env (TmRecFun fs e) k = do
  let binds = [(f, ContK (ProdK (cpsType t) (ContK (cpsType s)))) | TmFun f _ t s _ <- fs]
  let env' = foldr (uncurry Map.insert) env binds
  fs' <- traverse (cpsFun env') fs
  (e', t') <- cps env' e k
  let res = LetFunK fs' e'
  pure (res, t')
cps env (TmApp e1 e2) k =
  cps env e1 $ \ (TmVar v1) t1 -> do
    cps env e2 $ \v2 _t2 -> do
      s' <- case t1 of
        ContK (ProdK _t2' (ContK s')) -> pure s'
        _ -> error "bad function type"
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          (e', _t') <- k xv s'
          let res = LetContK [ContDef kv xv s' e'] (CallK (FnName v1) v2 kv)
          pure (res, s')
cps env (TmInl a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      (e', _t') <- k x (SumK ta tb)
      let res = LetValK x (InlK z) e'
      pure (res, SumK ta tb)
cps env (TmInr a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      (e', _t') <- k x (SumK ta tb)
      let res = LetValK x (InrK z) e'
      pure (res, SumK ta tb)
cps env (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps env e $ \z _t ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            let tl' = cpsType tl
            (el', sl') <- cpsTail (Map.insert xl tl' env) el j
            let tr' = cpsType tr
            (er', sr') <- cpsTail (Map.insert xr tr' env) er j
            let s' = fst (sl', sr')
            (e', _t') <- k x s'
            -- TODO: Case branches that accept multiple arguments at once
            let
              res = 
                LetContK [ContDef j x s' e'] $
                  LetContK [ContDef k1 (var xl) tl' el'] $
                    LetContK [ContDef k2 (var xr) tr' er'] $
                      CaseK z k1 k2
            pure (res, s')
cps env (TmPair e1 e2) k =
  cps env e1 $ \v1 t1 ->
    cps env e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        (e', _t') <- k x (ProdK t1 t2)
        let res = LetValK x (PairK v1 v2) e'
        pure (res, ProdK t1 t2)
cps env (TmFst e) k =
  cps env e $ \v t ->  do
    (ta, _tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      (e', _t') <- k x ta
      let res = LetFstK x v e'
      pure (res, ta)
cps env (TmSnd e) k =
  cps env e $ \v t -> do
    (_ta, tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      (e', _t') <- k x tb
      let res = LetSndK x v e'
      pure (res, tb)
cps _env TmNil k =
  freshTm "x" $ \x -> do
    (e', t') <- k x UnitK
    let res = LetValK x NilK e'
    pure (res, t')
cps _env (TmInt i) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x IntK
    let res = LetValK x (IntValK i) e'
    pure (res, t')
cps env (TmLet x t e1 e2) k = do
  let t' = cpsType t
  (e2', t2') <- cps (Map.insert x t' env) e2 k
  freshCo "j" $ \j -> do
    (e1', _t1') <- cpsTail env e1 j
    let res = LetContK [ContDef j (var x) t' e2'] e1'
    pure (res, t2')
cps env (TmAdd e1 e2) k =
  cps env e1 $ \x _t1 ->
    cps env e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z IntK
        let res = LetArithK z (AddK x y) e'
        pure (res, t')
cps env (TmSub e1 e2) k =
  cps env e1 $ \x _t1 ->
    cps env e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z IntK
        let res = LetArithK z (SubK x y) e'
        pure (res, t')
cps env (TmMul e1 e2) k =
  cps env e1 $ \x _t1 ->
    cps env e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z IntK
        let res = LetArithK z (MulK x y) e'
        pure (res, t')
cps env (TmIsZero e) k =
  cps env e $ \v _t -> -- t =~= IntK
    freshTm "x" $ \x -> do
      (e', t') <- k x (SumK UnitK UnitK)
      let res = LetIsZeroK x v e'
      pure (res, t')

cpsFun :: Map S.TmVar TypeK -> TmFun -> FreshM FunDef
cpsFun env (TmFun f x t s e) =
  freshCo "k" $ \k -> do
    -- Recursive bindings already handled, outside of this.
    let t' = cpsType t
    let s' = cpsType s
    (e', _s') <- cpsTail (Map.insert x t' env) e k
    let def = FunDef (fnName f) (var x) t' k (ContK s') e'
    pure def
  where fnName (S.TmVar y) = FnName y

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Map S.TmVar TypeK -> Term -> CoVar -> FreshM (TermK, TypeK)
cpsTail env (TmVarOcc x) k = case Map.lookup x env of
  Nothing -> error "variable not in scope"
  Just t' -> pure (JumpK k (var x), t')
cpsTail env (TmLam x t e) k =
  freshTm "f" $ \ (TmVar f) ->
    freshCo "k" $ \k' -> do
      let t' = cpsType t
      (e', s') <- cpsTail (Map.insert x t' env) e k'
      let fs = [FunDef (FnName f) (var x) t' k' s' e']
      let res = LetFunK fs (JumpK k (TmVar f))
      pure (res, ContK (ProdK t' (ContK s')))
cpsTail env (TmLet x t e1 e2) k =
  -- [[let x:t = e1 in e2]] k
  -- -->
  -- let j (x:t) = [[e2]] k; in [[e1]] j
  freshCo "j" $ \j -> do
    let t' = cpsType t
    (e2', _t2') <- cpsTail (Map.insert x t' env) e2 k
    (e1', t1') <- cpsTail env e1 j
    let res = LetContK [ContDef j (var x) t' e2'] e1'
    pure (res, t1')
cpsTail env (TmRecFun fs e) k = do
  let binds = [(f, cpsType (S.TyArr t s)) | TmFun f _x t s _e <- fs]
  let env' = foldr (uncurry Map.insert) env binds
  fs' <- traverse (cpsFun env') fs
  (e', t') <- cpsTail env' e k
  let res = LetFunK fs' e'
  pure (res, t')
cpsTail env (TmInl a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let res = LetValK x (InlK z) (JumpK k x)
      pure (res, SumK (cpsType a) (cpsType b))
cpsTail env (TmInr a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let res = LetValK x (InrK z) (JumpK k x)
      pure (res, SumK (cpsType a) (cpsType b))
cpsTail env (TmPair e1 e2) k =
  cps env e1 $ \v1 t1 ->
    cps env e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let res = LetValK x (PairK v1 v2) (JumpK k x)
        pure (res, ProdK t1 t2)
cpsTail env (TmFst e) k =
  cps env e $ \z t -> do
    (ta, _tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      let res = LetFstK x z (JumpK k x)
      pure (res, ta)
cpsTail env (TmSnd e) k =
  cps env e $ \z t -> do
    (_ta, tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      let res = LetSndK x z (JumpK k x)
      pure (res, tb)
cpsTail _env TmNil k =
  freshTm "x" $ \x -> do
    let res = LetValK x NilK (JumpK k x)
    pure (res, UnitK)
cpsTail _env (TmInt i) k =
  freshTm "x" $ \x -> do
    let res = LetValK x (IntValK i) (JumpK k x)
    pure (res, IntK)
cpsTail env (TmAdd e1 e2) k =
  cps env e1 $ \x _t1 -> -- t1 =~= IntK
    cps env e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetArithK z (AddK x y) (JumpK k z)
        pure (res, IntK)
cpsTail env (TmSub e1 e2) k =
  cps env e1 $ \x _t1 -> -- t1 =~= IntK
    cps env e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetArithK z (SubK x y) (JumpK k z)
        pure (res, IntK)
cpsTail env (TmMul e1 e2) k =
  cps env e1 $ \x _t1 -> -- t1 =~= IntK
    cps env e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetArithK z (MulK x y) (JumpK k z)
        pure (res, IntK)
cpsTail env (TmIsZero e) k =
  cps env e $ \z _t -> -- t =~= IntK
    freshTm "x" $ \x -> do
      let res = LetIsZeroK x z (JumpK k x)
      pure (res, SumK UnitK UnitK)
cpsTail env (TmApp e1 e2) k =
  cps env e1 $ \ (TmVar f) t1 -> -- t1 =~= t2 -> s
    cps env e2 $ \x _t2 -> do
      s <- case t1 of
        ContK (ProdK _t2' (ContK s)) -> pure s -- assert t2' === t2
        _ -> error "bad function type"
      let res = CallK (FnName f) x k
      pure (res, s)
cpsTail env (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps env e $ \z _t -> do
    -- _t === SumK (cpsType tl) (cpsType tr), because input is well-typed.
    freshCo "k1" $ \k1 ->
      freshCo "k2" $ \k2 -> do
        let tl' = cpsType tl
        (el', sl') <- cpsTail (Map.insert xl tl' env) el k
        let tr' = cpsType tr
        (er', sr') <- cpsTail (Map.insert xr tr' env) er k
        -- TODO: Case branches that accept multiple arguments at once
        let
          res =
            LetContK [ContDef k1 (var xl) tl' el'] $
              LetContK [ContDef k2 (var xr) tr' er'] $
                CaseK z k1 k2
        -- both branches have same type, so this is valid.
        -- (Alternatively, put `returns s` on Source.TmCase)
        let s' = fst (sl', sr')
        pure (res, s')


cpsMain :: Term -> (TermK, TypeK)
cpsMain e = runFresh $ cps Map.empty e (\z t -> pure (HaltK z, t))


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
pprintValue (IntValK i) = show i
pprintValue (InlK x) = "inl " ++ show x
pprintValue (InrK y) = "inr " ++ show y

pprintArith :: ArithK -> String
pprintArith (AddK x y) = show x ++ " + " ++ show y
pprintArith (SubK x y) = show x ++ " - " ++ show y
pprintArith (MulK x y) = show x ++ " * " ++ show y

pprintFunDef :: Int -> FunDef -> String
pprintFunDef n (FunDef f x t k s e) =
  indent n (show f ++ " " ++ pprintParam (show x) t ++ " " ++ pprintParam (show k) s ++ " =\n") ++ pprintTerm (n+2) e

pprintContDef :: Int -> ContDef -> String
pprintContDef n (ContDef k x t e) =
  indent n (show k ++ " " ++ pprintParam (show x) t ++ " =\n") ++ pprintTerm (n+2) e

pprintParam :: String -> TypeK -> String
pprintParam x t = "(" ++ x ++ " : " ++ pprintType t ++ ")"

pprintType :: TypeK -> String
pprintType (ContK t) = pprintAType t ++ " -> 0"
pprintType (ProdK t s) = pprintType t ++ " * " ++ pprintAType s
pprintType (SumK t s) = pprintType t ++ " + " ++ pprintAType s
pprintType IntK = "int"
pprintType UnitK = "unit"

pprintAType :: TypeK -> String
pprintAType IntK = "int"
pprintAType UnitK = "unit"
pprintAType t = "(" ++ pprintType t ++ ")"
