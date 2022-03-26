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
-- TODO: Should the type environment be considered part of the CPS monad? I kind of think so.
cps :: Map S.TmVar (TmVar, TypeK) -> Term -> (TmVar -> TypeK -> CPS (TermK (), TypeK)) -> CPS (TermK (), TypeK)
cps env (TmVarOcc x) k = case Map.lookup x env of
  Nothing -> error ("cps: variable not in scope: " ++ show x)
  Just (x', t) -> k x' t
cps env (TmLam x t e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      let x' = var x
      let t' = cpsType t
      (e', s') <- cpsTail (Map.insert x (x', t') env) e k'
      let fs = [FunDef () f [(x', t')] [(k', ContK [s'])] e']
      (e'', _t'') <- k f (FunK t' s')
      let res = LetFunK fs e''
      pure (res, FunK t' s')
cps env (TmRecFun fs e) k = do
  -- TODO: The names in these bindings should be added to the freshening scope.
  -- (Or they should be freshened, if an inner and outer recursive definition
  -- have the same name)
  let binds = [(f, (var f, cpsType (S.TyArr t s))) | TmFun f _ t s _ <- fs]
  let env' = foldr (uncurry Map.insert) env binds
  fs' <- traverse (cpsFun env') fs
  (e', t') <- cps env' e k
  let res = LetFunK fs' e'
  pure (res, t')
cps env (TmApp e1 e2) k =
  cps env e1 $ \v1 t1 -> do
    cps env e2 $ \v2 _t2 -> do
      s' <- case t1 of
        FunK _t2' s' -> pure s'
        _ -> error ("bad function type: " ++ pprintType t1)
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          (e', _t') <- k xv s'
          let res = LetContK [ContDef () kv [(xv, s')] e'] (CallK v1 [v2] [kv])
          pure (res, s')
cps env (TmInl a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      (e', _t') <- k x (SumK ta tb)
      let res = LetValK x (SumK ta tb) (InlK z) e'
      pure (res, SumK ta tb)
cps env (TmInr a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      (e', _t') <- k x (SumK ta tb)
      let res = LetValK x (SumK ta tb) (InrK z) e'
      pure (res, SumK ta tb)
cps env (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps env e $ \z _t ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            let xl' = var xl
            let tl' = cpsType tl
            (el', sl') <- cpsTail (Map.insert xl (xl', tl') env) el j
            let xr' = var xr
            let tr' = cpsType tr
            (er', sr') <- cpsTail (Map.insert xr (xr', tr') env) er j
            let s' = fst (sl', sr')
            (e', _t') <- k x s'
            -- TODO: Case branches that accept multiple arguments at once
            let
              res = 
                LetContK [ContDef () j [(x, s')] e'] $
                  LetContK [ContDef () k1 [(xl', tl')] el'] $
                    LetContK [ContDef () k2 [(xr', tr')] er'] $
                      CaseK z k1 (ContK [tl']) k2 (ContK [tr'])
            pure (res, s')
cps env (TmIf e et ef) k =
  cps env e $ \z _t -> -- t =~= BoolK
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            (et', st') <- cpsTail env et j
            (ef', sf') <- cpsTail env ef j
            let s' = fst (st', sf')
            (e', _t') <- k x s'
            let
              res =
                LetContK [ContDef () j [(x, s')] e'] $
                  LetContK [ContDef () k1 [] et'] $
                    LetContK [ContDef () k2 [] ef'] $
                      -- NOTE: k2, k1 is the correct order here.
                      -- This is because case branches are laid out in order of discriminant.
                      -- false = 0, true = 1, so the branches should be laid
                      -- out as false, true as oppose to the source order true,
                      -- false.
                      CaseK z k2 (ContK []) k1 (ContK [])
            pure (res, s')
cps _env (TmBool b) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x BoolK
    let res = LetValK x BoolK (BoolValK b) e'
    pure (res, t')
cps env (TmPair e1 e2) k =
  cps env e1 $ \v1 t1 ->
    cps env e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        (e', _t') <- k x (ProdK t1 t2)
        let res = LetValK x (ProdK t1 t2) (PairK v1 v2) e'
        pure (res, ProdK t1 t2)
cps env (TmFst e) k =
  cps env e $ \v t ->  do
    (ta, _tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      (e', _t') <- k x ta
      let res = LetFstK x ta v e'
      pure (res, ta)
cps env (TmSnd e) k =
  cps env e $ \v t -> do
    (_ta, tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      (e', _t') <- k x tb
      let res = LetSndK x tb v e'
      pure (res, tb)
cps _env TmNil k =
  freshTm "x" $ \x -> do
    (e', t') <- k x UnitK
    let res = LetValK x UnitK NilK e'
    pure (res, t')
cps _env (TmInt i) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x IntK
    let res = LetValK x IntK (IntValK i) e'
    pure (res, t')
cps env (TmLet x t e1 e2) k = do
  let x' = var x
  let t' = cpsType t
  (e2', t2') <- cps (Map.insert x (x', t') env) e2 k
  freshCo "j" $ \j -> do
    (e1', _t1') <- cpsTail env e1 j
    let res = LetContK [ContDef () j [(x', t')] e2'] e1'
    pure (res, t2')
cps env (TmArith e1 op e2) k =
  cps env e1 $ \x _t1 ->
    cps env e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z IntK
        let res = LetArithK z (makeArith op x y) e'
        pure (res, t')
cps env (TmCmp e1 cmp e2) k =
  cps env e1 $ \x _t1 ->
    cps env e2 $ \y _t2 ->
      freshTm "z" $ \z -> do
        (e', t') <- k z BoolK
        let res = LetCompareK z (makeCompare cmp x y) e'
        pure (res, t')

cpsFun :: Map S.TmVar (TmVar, TypeK) -> TmFun -> CPS (FunDef ())
cpsFun env (TmFun f x t s e) =
  freshCo "k" $ \k -> do
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable?)"
      Just (f', _) -> pure f'
    let x' = var x
    let t' = cpsType t
    let s' = cpsType s
    (e', _s') <- cpsTail (Map.insert x (x', t') env) e k
    let def = FunDef () f' [(x', t')] [(k, ContK [s'])] e'
    pure def

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Map S.TmVar (TmVar, TypeK) -> Term -> CoVar -> CPS (TermK (), TypeK)
cpsTail env (TmVarOcc x) k = case Map.lookup x env of
  Nothing -> error ("cpsTail: variable not in scope: " ++ show x)
  Just (x', t') -> pure (JumpK k [x'], t')
cpsTail env (TmLam x t e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      let x' = var x
      let t' = cpsType t
      (e', s') <- cpsTail (Map.insert x (x', t') env) e k'
      let fs = [FunDef () f [(x', t')] [(k', ContK [s'])] e']
      let res = LetFunK fs (JumpK k [f])
      pure (res, FunK t' s')
cpsTail env (TmLet x t e1 e2) k =
  -- [[let x:t = e1 in e2]] k
  -- -->
  -- let j (x:t) = [[e2]] k; in [[e1]] j
  freshCo "j" $ \j -> do
    let x' = var x
    let t' = cpsType t
    (e2', _t2') <- cpsTail (Map.insert x (x', t') env) e2 k
    (e1', t1') <- cpsTail env e1 j
    let res = LetContK [ContDef () j [(x', t')] e2'] e1'
    pure (res, t1')
cpsTail env (TmRecFun fs e) k = do
  let binds = [(f, (var f, cpsType (S.TyArr t s))) | TmFun f _x t s _e <- fs]
  let env' = foldr (uncurry Map.insert) env binds
  fs' <- traverse (cpsFun env') fs
  (e', t') <- cpsTail env' e k
  let res = LetFunK fs' e'
  pure (res, t')
cpsTail env (TmInl a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      let res = LetValK x (SumK ta tb) (InlK z) (JumpK k [x])
      pure (res, SumK ta tb)
cpsTail env (TmInr a b e) k =
  cps env e $ \z _t ->
    freshTm "x" $ \x -> do
      let ta = cpsType a
      let tb = cpsType b
      let res = LetValK x (SumK ta tb) (InrK z) (JumpK k [x])
      pure (res, SumK ta tb)
cpsTail env (TmPair e1 e2) k =
  cps env e1 $ \v1 t1 ->
    cps env e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let res = LetValK x (ProdK t1 t2) (PairK v1 v2) (JumpK k [x])
        pure (res, ProdK t1 t2)
cpsTail env (TmFst e) k =
  cps env e $ \z t -> do
    (ta, _tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      let res = LetFstK x ta z (JumpK k [x])
      pure (res, ta)
cpsTail env (TmSnd e) k =
  cps env e $ \z t -> do
    (_ta, tb) <- case t of
      ProdK ta tb -> pure (ta, tb)
      _ -> error "bad projection"
    freshTm "x" $ \x -> do
      let res = LetSndK x tb z (JumpK k [x])
      pure (res, tb)
cpsTail _env TmNil k =
  freshTm "x" $ \x -> do
    let res = LetValK x UnitK NilK (JumpK k [x])
    pure (res, UnitK)
cpsTail _env (TmInt i) k =
  freshTm "x" $ \x -> do
    let res = LetValK x IntK (IntValK i) (JumpK k [x])
    pure (res, IntK)
cpsTail env (TmArith e1 op e2) k =
  cps env e1 $ \x _t1 -> -- t1 =~= IntK
    cps env e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetArithK z (makeArith op x y) (JumpK k [z])
        pure (res, IntK)
cpsTail env (TmCmp e1 cmp e2) k =
  cps env e1 $ \x _t1 -> -- t1 =~= IntK
    cps env e2 $ \y _t2 -> -- t2 =~= IntK
      freshTm "z" $ \z -> do
        let res = LetCompareK z (makeCompare cmp x y) (JumpK k [z])
        pure (res, BoolK)
cpsTail env (TmApp e1 e2) k =
  cps env e1 $ \f t1 -> -- t1 =~= t2 -> s
    cps env e2 $ \x _t2 -> do
      s' <- case t1 of
        FunK _t2' s' -> pure s'
        _ -> error ("bad function type: " ++ pprintType t1)
      let res = CallK f [x] [k]
      pure (res, s')
cpsTail env (TmCase e (xl, tl, el) (xr, tr, er)) k =
  cps env e $ \z _t -> do
    -- _t === SumK (cpsType tl) (cpsType tr), because input is well-typed.
    freshCo "k1" $ \k1 ->
      freshCo "k2" $ \k2 -> do
        let xl' = var xl
        let tl' = cpsType tl
        (el', sl') <- cpsTail (Map.insert xl (xl', tl') env) el k
        let xr' = var xr
        let tr' = cpsType tr
        (er', sr') <- cpsTail (Map.insert xr (xr', tr') env) er k
        -- TODO: Case branches that accept multiple arguments at once
        let
          res =
            LetContK [ContDef () k1 [(xl', tl')] el'] $
              LetContK [ContDef () k2 [(xr', tr')] er'] $
                CaseK z k1 (ContK [tl']) k2 (ContK [tr'])
        -- both branches have same type, so this is valid.
        -- (Alternatively, put `returns s` on Source.TmCase)
        let s' = fst (sl', sr')
        pure (res, s')
cpsTail env (TmIf e et ef) k =
  cps env e $ \z _t -> do
    freshCo "k1" $ \k1 ->
      freshCo "k2" $ \k2 -> do
        (et', st') <- cpsTail env et k
        (ef', sf') <- cpsTail env ef k
        let s' = fst (st', sf')
        let
          -- NOTE: k2, k1 is the correct order here.
          -- This is because case branches are laid out in order of discriminant.
          -- false = 0, true = 1, so the branches should be laid
          -- out as false, true as oppose to the source order true,
          -- false.
          res =
            LetContK [ContDef () k1 [] et'] $
              LetContK [ContDef () k2 [] ef'] $
                CaseK z k2 (ContK []) k1 (ContK [])
        pure (res, s')
cpsTail _env (TmBool b) k =
  freshTm "x" $ \x ->
    pure (LetValK x BoolK (BoolValK b) (JumpK k [x]), BoolK)


cpsMain :: Term -> (TermK (), TypeK)
cpsMain e = runFresh $ cps Map.empty e (\z t -> pure (HaltK z, t))


-- TODO: Monad that stores both in-scope set and typing environment
-- data CPSEnv = CPSEnv { cpsEnvScope :: Map String Int, cpsEnvCtx :: Map TmVar TypeK }

data CPSEnv = CPSEnv { cpsEnvScope :: Map String Int }

emptyEnv :: CPSEnv
emptyEnv = CPSEnv Map.empty

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
  let extend (CPSEnv sc) = CPSEnv (Map.insert x (i+1) sc)
  local extend (k x')

freshCo :: String -> (CoVar -> CPS a) -> CPS a
freshCo x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = CoVar (x ++ show i)
  let extend (CPSEnv sc) = CPSEnv (Map.insert x (i+1) sc)
  local extend (k x')

-- freshVarBind :: S.TmVar -> S.Type -> ((TmVar, TypeK) -> CPS a) -> CPS a
-- freshVarBind (S.TmVar x) t k =
--   freshTm x $ \x' -> do
--     let t' = cpsType t
--     k (x', t')

-- -- Hang on, if I rename the functions to avoid shadowing existing definitions,
-- -- that means I need to rename occurrences of these functions in the body of
-- -- the `let fun` binding. AARGH.
-- -- I guess that means I need to lookup the subst at TmVarOcc? Do I have to
-- -- worry about passing under binders?
-- --
-- -- ... Can I *not* rename the functions, just add them to the scope?
-- -- (Actually, I only need a S.TmVar -> TmVar map, which is easier to deal with.)
-- freshenFns :: [TmFun] -> ([TmFun] -> CPS a) -> CPS a
-- freshenFns fs k = do
--   scope <- ask
--   let
--     freshen sc (TmFun (S.TmVar f) x s t e) =
--       let i = fromMaybe 0 (Map.lookup x sc) in
--       let f' = TmVar f i in
--       (Map.insert x (i+1) sc, TmFun f' x s t e)
--   let (scope', fs') = mapAccumL freshen scope fs
--   let extend sc = scope'
--   local extend (k fs')

runFresh :: CPS a -> a
runFresh = flip runReader emptyEnv . runCPS


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
