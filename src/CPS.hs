{-# LANGUAGE StandaloneDeriving, DerivingVia, FlexibleInstances, MultiParamTypeClasses #-}

module CPS
    ( TermK(..)
    , TmVar(..)
    , CoVar(..)
    , FunDef(..)
    , ContDef(..)
    , ArithK(..)
    , CmpK(..)
    , ValueK(..)

    , TypeK(..)

    , cpsMain
    , pprintTerm
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

import Control.Monad.Reader

import qualified Source as S
import Source (Term(..), TmFun(..), TmArith(..), TmCmp(..))

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
-- Continuations are second-class, so they get a different type. (I collapse
-- the distinction between them later on, but maybe there's a more efficient
-- way to do jumps...)
data TmVar = TmVar String Int
  deriving (Eq, Ord)
newtype CoVar = CoVar String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x i) = x ++ show i
instance Show CoVar where
  show (CoVar k) = k

-- | Terms in continuation-passing style.
--
-- CPS terms are basically (named, parametrized) basic blocks: a list of
-- assignments terminated by a control flow transfer.
--
-- (Actually, I think this IR is technically or nearly in ANF)
data TermK a
  -- Assignments
  -- let val x:t = v in e
  = LetValK TmVar TypeK ValueK (TermK a)
  -- let x:t = fst y in e
  | LetFstK TmVar TypeK TmVar (TermK a)
  -- let x:t = snd y in e
  | LetSndK TmVar TypeK TmVar (TermK a)
  -- let z = x + y in e
  | LetArithK TmVar ArithK (TermK a)
  -- let z = x `cmp` y in e 
  | LetCompareK TmVar CmpK (TermK a)

  -- let rec ks in e
  | LetContK [ContDef a] (TermK a)
  -- let rec fs in e
  | LetFunK [FunDef a] (TermK a)

  -- Block terminators
  -- k x..., goto k(x...)
  | JumpK CoVar [TmVar]
  -- f x k, call f(x, k)
  | CallK TmVar [TmVar] [CoVar]
  -- case x of k1 : s1 | k2 : s2, branch
  | CaseK TmVar CoVar TypeK CoVar TypeK
  -- halt x
  | HaltK TmVar

-- | Named basic blocks
-- @k (x:τ)+ := e@
data ContDef a = ContDef a CoVar [(TmVar, TypeK)] (TermK a)

-- | Function definitions
-- @f (x:τ) (k:σ) := e@
data FunDef a = FunDef  a TmVar [(TmVar, TypeK)] [(CoVar, TypeK)] (TermK a)

-- | Values require no evaluation.
data ValueK
  = NilK
  | PairK TmVar TmVar
  | InlK TmVar
  | InrK TmVar
  | IntValK Int
  | BoolValK Bool

data ArithK
  = AddK TmVar TmVar
  | SubK TmVar TmVar
  | MulK TmVar TmVar

makeArith :: TmArith -> TmVar -> TmVar -> ArithK
makeArith TmArithAdd x y = AddK x y
makeArith TmArithSub x y = SubK x y
makeArith TmArithMul x y = MulK x y

data CmpK
  = CmpEqK TmVar TmVar
  | CmpNeK TmVar TmVar
  | CmpLtK TmVar TmVar
  | CmpLeK TmVar TmVar
  | CmpGtK TmVar TmVar
  | CmpGeK TmVar TmVar

makeCompare :: TmCmp -> TmVar -> TmVar -> CmpK
makeCompare TmCmpEq x y = CmpEqK x y
makeCompare TmCmpNe x y = CmpNeK x y
makeCompare TmCmpLt x y = CmpLtK x y
makeCompare TmCmpLe x y = CmpLeK x y
makeCompare TmCmpGt x y = CmpGtK x y
makeCompare TmCmpGe x y = CmpGeK x y

data TypeK
  -- unit
  = UnitK
  -- int
  | IntK
  -- bool
  | BoolK
  -- σ × τ
  | ProdK TypeK TypeK
  -- σ + τ
  | SumK TypeK TypeK
  -- (σ1, ..., σn) -> 0
  -- The type of a continuation
  | ContK [TypeK]
  -- (τ * σ -> 0) -> 0
  -- The type of a function.
  | FunK TypeK TypeK

cpsType :: S.Type -> TypeK
cpsType S.TyUnit = UnitK
cpsType S.TyInt = IntK
cpsType S.TyBool = BoolK
cpsType (S.TySum a b) = SumK (cpsType a) (cpsType b)
cpsType (S.TyProd a b) = ProdK (cpsType a) (cpsType b)
cpsType (S.TyArr a b) = FunK (cpsType a) (cpsType b)
cpsType (S.TyVarOcc _) = error "not implemented: polymorphic cpsType"
cpsType (S.TyAll _ _) = error "not implemented: polymorphic cpsType"

contDefType :: ContDef a -> TypeK
contDefType (ContDef _ _ xs _) = ContK (map snd xs)

funDefType :: FunDef a -> TypeK
funDefType (FunDef _ _ [x] [k] _) = FunK (snd x) (snd k)
funDefType (FunDef _ _ _ _ _) = error "not supported: function with multiple params/conts"


-- TODO: I dislike this. It technically works, because shadowed source becomes
-- shadowed CPS, but if I ever start renaming bound variables, it's going to
-- fall apart.
--
-- Add a @Map S.TmVar TmVar@ to the CPS environment. (that parallels @Map S.TmVar TypeK@?)
var :: S.TmVar -> TmVar
var (S.TmVar x) = TmVar x 0

-- TODO: This actually has most elements of a type checker.
-- Maybe I should add Except and error-reporting?

-- | CPS-convert a term.
--
-- TODO: Find a way to reduce the nesting. ContT, maybe?
cps :: Term -> (TmVar -> TypeK -> CPS (TermK (), TypeK)) -> CPS (TermK (), TypeK)
cps (TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error ("cps: variable not in scope: " ++ show x)
    Just (x', t) -> k x' t
cps (TmLam x t e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBind x t $ \ (x', t') -> do
        (e', s') <- withVarBinds [(x, (x', t'))] $ cpsTail e k'
        let fun = FunDef () f [(x', t')] [(k', ContK [s'])] e'
        pure (fun, FunK t' s')
      (e'', _t'') <- k f ty
      pure (LetFunK [fun] e'', ty)
cps (TmRecFun fs e) k = do
  -- TODO: The names in these bindings should be added to the freshening scope.
  -- (Or they should be freshened, if an inner and outer recursive definition
  -- have the same name)
  let binds = [(f, (var f, cpsType (S.TyArr t s))) | TmFun f _ t s _ <- fs]
  fs' <- withVarBinds binds $ traverse cpsFun fs
  (e', t') <- withVarBinds binds $ cps e k
  let res = LetFunK fs' e'
  pure (res, t')
cps (TmApp e1 e2) k =
  cps e1 $ \v1 t1 -> do
    cps e2 $ \v2 _t2 -> do
      s' <- case t1 of
        FunK _t2' s' -> pure s'
        _ -> error ("bad function type: " ++ pprintType t1)
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          (e', _t') <- k xv s'
          let res = LetContK [ContDef () kv [(xv, s')] e'] (CallK v1 [v2] [kv])
          pure (res, s')
cps (TmInl a b e) k =
  cps e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      (e', _t') <- k x (SumK ta tb)
      let res = LetValK x (SumK ta tb) (InlK z) e'
      pure (res, SumK ta tb)
cps (TmInr a b e) k =
  cps e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      (e', _t') <- k x (SumK ta tb)
      let res = LetValK x (SumK ta tb) (InrK z) e'
      pure (res, SumK ta tb)
cps (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z _t ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            (kont1, sl') <- cpsBranch k1 [(xl, tl)] el j
            (kont2, sr') <- cpsBranch k2 [(xr, tr)] er j
            let s' = fst (sl', sr')
            (e', _t') <- k x s'
            -- TODO: Case branches that accept multiple arguments at once
            let
              res = 
                LetContK [ContDef () j [(x, s')] e'] $
                  LetContK [kont1] $
                    LetContK [kont2] $
                      CaseK z k1 (contDefType kont1) k2 (contDefType kont2)
            pure (res, s')
cps (TmIf e et ef) k =
  cps e $ \z _t -> -- t =~= BoolK
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            (kont1, st') <- cpsBranch k1 [] et j
            (kont2, sf') <- cpsBranch k2 [] ef j
            let s' = fst (st', sf')
            (e', _t') <- k x s'
            let
              res =
                LetContK [ContDef () j [(x, s')] e'] $
                  LetContK [kont1] $
                    LetContK [kont2] $
                      -- NOTE: k2, k1 is the correct order here.
                      -- This is because case branches are laid out in order of discriminant.
                      -- false = 0, true = 1, so the branches should be laid
                      -- out as false, true as oppose to the source order true,
                      -- false.
                      CaseK z k2 (contDefType kont2) k1 (contDefType kont1)
            pure (res, s')
cps (TmBool b) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x BoolK
    let res = LetValK x BoolK (BoolValK b) e'
    pure (res, t')
cps (TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        (e', _t') <- k x (ProdK t1 t2)
        let res = LetValK x (ProdK t1 t2) (PairK v1 v2) e'
        pure (res, ProdK t1 t2)
cps (TmFst e) k =
  cps e $ \v t ->  do
    (ta, _tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      (e', _t') <- k x ta
      let res = LetFstK x ta v e'
      pure (res, ta)
cps (TmSnd e) k =
  cps e $ \v t -> do
    (_ta, tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      (e', _t') <- k x tb
      let res = LetSndK x tb v e'
      pure (res, tb)
cps TmNil k =
  freshTm "x" $ \x -> do
    (e', t') <- k x UnitK
    let res = LetValK x UnitK NilK e'
    pure (res, t')
cps (TmInt i) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x IntK
    let res = LetValK x IntK (IntValK i) e'
    pure (res, t')
cps (TmLet x t e1 e2) k = do
  let x' = var x
  let t' = cpsType t
  (e2', t2') <- withVarBinds [(x, (x', t'))] $ cps e2 k
  freshCo "j" $ \j -> do
    (e1', _t1') <- cpsTail e1 j
    let res = LetContK [ContDef () j [(x', t')] e2'] e1'
    pure (res, t2')
cps (TmArith e1 op e2) k =
  cps e1 $ \x _t1 ->
    cps e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z IntK
        let res = LetArithK z (makeArith op x y) e'
        pure (res, t')
cps (TmCmp e1 cmp e2) k =
  cps e1 $ \x _t1 ->
    cps e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z BoolK
        let res = LetCompareK z (makeCompare cmp x y) e'
        pure (res, t')

cpsFun :: TmFun -> CPS (FunDef ())
cpsFun (TmFun f x t s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable?)"
      Just (f', _) -> pure f'
    let x' = var x
    let t' = cpsType t
    let s' = cpsType s
    (e', _s') <- withVarBinds [(x, (x', t'))] $ cpsTail e k
    let def = FunDef () f' [(x', t')] [(k, ContK [s'])] e'
    pure def

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Term -> CoVar -> CPS (TermK (), TypeK)
cpsTail (TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error ("cpsTail: variable not in scope: " ++ show x)
    Just (x', t') -> pure (JumpK k [x'], t')
cpsTail (TmLam x t e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBind x t $ \ (x', t') -> do
        (e', s') <- withVarBinds [(x, (x', t'))] $ cpsTail e k'
        let fun = FunDef () f [(x', t')] [(k', ContK [s'])] e'
        pure (fun, FunK t' s')
      let res = LetFunK [fun] (JumpK k [f])
      pure (res, ty)
cpsTail (TmLet x t e1 e2) k =
  -- [[let x:t = e1 in e2]] k
  -- -->
  -- let j (x:t) = [[e2]] k; in [[e1]] j
  -- (This is similar to, but not quite the same as @case e1 of x:t -> e2@)
  freshCo "j" $ \j -> do
    (kont, t2') <- cpsBranch j [(x, t)] e2 k
    (e1', _t1') <- cpsTail e1 j
    pure (LetContK [kont] e1', t2')
cpsTail (TmRecFun fs e) k = do
  let binds = [(f, (var f, cpsType (S.TyArr t s))) | TmFun f _x t s _e <- fs]
  fs' <- withVarBinds binds $ traverse cpsFun fs
  (e', t') <- withVarBinds binds $ cpsTail e k
  let res = LetFunK fs' e'
  pure (res, t')
cpsTail (TmInl a b e) k =
  cps e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      let res = LetValK x (SumK ta tb) (InlK z) (JumpK k [x])
      pure (res, SumK ta tb)
cpsTail (TmInr a b e) k =
  cps e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      let res = LetValK x (SumK ta tb) (InrK z) (JumpK k [x])
      pure (res, SumK ta tb)
cpsTail (TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let res = LetValK x (ProdK t1 t2) (PairK v1 v2) (JumpK k [x])
        pure (res, ProdK t1 t2)
cpsTail (TmFst e) k =
  cps e $ \z t -> do
    (ta, _tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      let res = LetFstK x ta z (JumpK k [x])
      pure (res, ta)
cpsTail (TmSnd e) k =
  cps e $ \z t -> do
    (_ta, tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      let res = LetSndK x tb z (JumpK k [x])
      pure (res, tb)
cpsTail TmNil k =
  freshTm "x" $ \x -> do
    let res = LetValK x UnitK NilK (JumpK k [x])
    pure (res, UnitK)
cpsTail (TmInt i) k =
  freshTm "x" $ \x -> do
    let res = LetValK x IntK (IntValK i) (JumpK k [x])
    pure (res, IntK)
cpsTail (TmArith e1 op e2) k =
  cps e1 $ \x _t1 -> -- t1 =~= IntK
    cps e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetArithK z (makeArith op x y) (JumpK k [z])
        pure (res, IntK)
cpsTail (TmCmp e1 cmp e2) k =
  cps e1 $ \x _t1 -> -- t1 =~= IntK
    cps e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetCompareK z (makeCompare cmp x y) (JumpK k [z])
        pure (res, BoolK)
cpsTail (TmApp e1 e2) k =
  cps e1 $ \f t1 -> -- t1 =~= t2 -> s
    cps e2 $ \x _t2 -> do
      s' <- case t1 of
        FunK _t2' s' -> pure s'
        _ -> error ("bad function type: " ++ pprintType t1)
      let res = CallK f [x] [k]
      pure (res, s')
cpsTail (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z _t -> do
    -- _t === SumK (cpsType tl) (cpsType tr), because input is well-typed.
    freshCo "k1" $ \k1 ->
      freshCo "k2" $ \k2 -> do
        (kont1, sl') <- cpsBranch k1 [(xl, tl)] el k
        (kont2, sr') <- cpsBranch k2 [(xr, tr)] er k
        -- TODO: Case branches that accept multiple arguments at once
        let
          res =
            LetContK [kont1] $
              LetContK [kont2] $
                CaseK z k1 (contDefType kont1) k2 (contDefType kont2)
        -- both branches have same type, so this is valid.
        -- (Alternatively, put `returns s` on Source.TmCase)
        let s' = fst (sl', sr')
        pure (res, s')
cpsTail (TmIf e et ef) k =
  cps e $ \z _t -> do
    freshCo "k1" $ \k1 ->
      freshCo "k2" $ \k2 -> do
        (kont1, st') <- cpsBranch k1 [] et k
        (kont2, sf') <- cpsBranch k2 [] ef k
        let s' = fst (st', sf')
        let
          -- NOTE: k2, k1 is the correct order here.
          -- This is because case branches are laid out in order of discriminant.
          -- false = 0, true = 1, so the branches should be laid
          -- out as false, true as oppose to the source order true,
          -- false.
          res =
            LetContK [kont1] $
              LetContK [kont2] $
                CaseK z k2 (contDefType kont2) k1 (contDefType kont1)
        pure (res, s')
cpsTail (TmBool b) k =
  freshTm "x" $ \x ->
    pure (LetValK x BoolK (BoolValK b) (JumpK k [x]), BoolK)


cpsMain :: Term -> (TermK (), TypeK)
cpsMain e = flip runReader emptyEnv $ runCPS $
  cps e (\z t -> pure (HaltK z, t))


-- | CPS-transform a case alternative @(x:t)+ -> e@.
--
-- @cpsBranch k xs e j@ returns @(cont k xs = [[e]] j; s)@ where @s@ is the
-- type of @e@.
cpsBranch :: CoVar -> [(S.TmVar, S.Type)] -> Term -> CoVar -> CPS (ContDef (), TypeK)
cpsBranch k [(x, t)] e j = freshenVarBind x t $ \ (x', t') -> do
  (e', s') <- withVarBinds [(x, (x', t'))] $ cpsTail e j
  pure (ContDef () k [(x', t')] e', s')
cpsBranch k [] e j = do
  -- TODO: This is/should be an instance of the general version where xs = [].
  -- I think it is, because withVarBinds [] is no-op. (and freshenVarBinds
  -- should also be no-op)
  (e', s') <- cpsTail e j
  pure (ContDef () k [] e', s')
cpsBranch _ _ _ _ = error "multi-argument case branches not yet supported"


data CPSEnv = CPSEnv { cpsEnvScope :: Map String Int, cpsEnvCtx :: Map S.TmVar (TmVar, TypeK) }

emptyEnv :: CPSEnv
emptyEnv = CPSEnv Map.empty Map.empty

newtype CPS a = CPS { runCPS :: Reader CPSEnv a }

deriving via Reader CPSEnv instance Functor CPS
deriving via Reader CPSEnv instance Applicative CPS
deriving via Reader CPSEnv instance Monad CPS
deriving via Reader CPSEnv instance MonadReader CPSEnv CPS

freshTm :: String -> (TmVar -> CPS a) -> CPS a
freshTm x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = TmVar x i
  let extend (CPSEnv sc ctx) = CPSEnv (Map.insert x (i+1) sc) ctx
  local extend (k x')

freshCo :: String -> (CoVar -> CPS a) -> CPS a
freshCo x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = CoVar (x ++ show i)
  let extend (CPSEnv sc ctx) = CPSEnv (Map.insert x (i+1) sc) ctx
  local extend (k x')

-- TODO: Rather than require the user to provide TmVar and TypeK, this function
-- should freshen the variables and CPS-convert the types. (Return the updated
-- binds through a continuation argument?)
withVarBinds :: [(S.TmVar, (TmVar, TypeK))] -> CPS a -> CPS a
withVarBinds binds m = local extend m
  where
    -- TODO: This should update the in-scope set, so we don't have problems
    -- with shadowing definitions and parameters.
    extend (CPSEnv sc ctx) = CPSEnv sc (extendCtx binds ctx)

-- TODO: *Actually* freshen the binder here.
-- (Currently, this is just the same as @let (x', t') = (var x, cpsType t) in e@)
freshenVarBind :: S.TmVar -> S.Type -> ((TmVar, TypeK) -> CPS a) -> CPS a
freshenVarBind x t k = k (var x, cpsType t)

extendCtx :: [(S.TmVar, (TmVar, TypeK))] -> Map S.TmVar (TmVar, TypeK) -> Map S.TmVar (TmVar, TypeK)
extendCtx binds env = foldr (uncurry Map.insert) env binds


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermK a -> String
pprintTerm n (HaltK x) = indent n $ "halt " ++ show x ++ ";\n"
pprintTerm n (JumpK k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallK f xs ks) = indent n $ show f ++ " " ++ intercalate " " (map show xs ++ map show ks) ++ ";\n"
pprintTerm n (CaseK x k1 s1 k2 s2) =
  indent n $ "case " ++ show x ++ " of " ++ show k1 ++ " | " ++ show k2 ++ ";\n"
pprintTerm n (LetValK x t v e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFunK fs e) =
  indent n "letfun\n" ++ concatMap (pprintFunDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContK ks e) =
  indent n "letcont\n" ++ concatMap (pprintContDef (n+2)) ks ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetFstK x t y e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndK x t y e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetArithK x op e) =
  indent n ("let " ++ show x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareK x cmp e) =
  indent n ("let " ++ show x ++ " = " ++ pprintCompare cmp ++ ";\n") ++ pprintTerm n e

pprintValue :: ValueK -> String
pprintValue NilK = "()"
pprintValue (PairK x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntValK i) = show i
pprintValue (BoolValK b) = if b then "true" else "false"
pprintValue (InlK x) = "inl " ++ show x
pprintValue (InrK y) = "inr " ++ show y

pprintArith :: ArithK -> String
pprintArith (AddK x y) = show x ++ " + " ++ show y
pprintArith (SubK x y) = show x ++ " - " ++ show y
pprintArith (MulK x y) = show x ++ " * " ++ show y

pprintCompare :: CmpK -> String
pprintCompare (CmpEqK x y) = show x ++ " == " ++ show y
pprintCompare (CmpNeK x y) = show x ++ " != " ++ show y
pprintCompare (CmpLtK x y) = show x ++ " < " ++ show y
pprintCompare (CmpLeK x y) = show x ++ " <= " ++ show y
pprintCompare (CmpGtK x y) = show x ++ " > " ++ show y
pprintCompare (CmpGeK x y) = show x ++ " >= " ++ show y

pprintFunDef :: Int -> FunDef a -> String
pprintFunDef n (FunDef _ f xs ks e) =
  indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    -- One parameter list or two?
    params = "(" ++ intercalate ", " (map pprintTmParam xs ++ map pprintCoParam ks) ++ ")"
    pprintTmParam (x, t) = show x ++ " : " ++ pprintType t
    pprintCoParam (k, s) = show k ++ " : " ++ pprintType s

pprintContDef :: Int -> ContDef a -> String
pprintContDef n (ContDef _ k xs e) =
  indent n (show k ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " (map pprintTmParam xs) ++ ")"
    pprintTmParam :: (TmVar, TypeK) -> String
    pprintTmParam (x, t) = show x ++ " : " ++ pprintType t

pprintType :: TypeK -> String
pprintType (ContK ts) = "(" ++ intercalate ", " params ++ ") -> 0"
  where params = map pprintType ts
pprintType (FunK t s) = pprintType (ContK [t, ContK [s]])
pprintType (ProdK t s) = pprintType t ++ " * " ++ pprintAType s
pprintType (SumK t s) = pprintType t ++ " + " ++ pprintAType s
pprintType IntK = "int"
pprintType UnitK = "unit"
pprintType BoolK = "bool"

pprintAType :: TypeK -> String
pprintAType IntK = "int"
pprintAType UnitK = "unit"
pprintAType t = "(" ++ pprintType t ++ ")"
