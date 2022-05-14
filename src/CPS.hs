
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
    , pprintType
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Traversable (mapAccumL, for)
import Data.Bifunctor

import Control.Monad.Reader
import Control.Monad.Except

import qualified Source as S
import Source (Term(..), TmFun(..), TmArith(..), TmCmp(..))

-- TODO: letrec (f : t -> s = e)+ in e', but check when CPSing that e has form '\ (x:t) -> rhs'.
-- (Basically, desugar it to let fun (f (x : t) : s = rhs)+ in e')

-- call/cc: pass function return continuation to argument?
-- what if call/cc in contdef? in let-binding?
--
-- Maybe
--   fun callcc f k = f k k;
-- ?
-- I think that's the CPS representation, but I don't know how the source-level
-- version of the CPS translation works.
--
-- Typing rule for call/cc is Pierce's Law or something?
-- (((a -> b) -> a) -> a)
-- Shows that the original continuation (b) is discarded.
--
-- CPS transform for shift/reset?
-- Actually, not really. call/cc and control effects cause computational impurity,
-- which I don't want to deal with right now. Even if 'reset' can be used to
-- encapsulate the impurity.
-- Also, standard CPS is insufficient for delimited control. (CPS: can invoke a
-- continuation. shift/reset: need to split, compose, and invoke continuations)


-- All sorts of variables exist in the same namespace.
-- Continuations are second-class, so they get a different type. (I collapse
-- the distinction between them later on, but maybe there's a more efficient
-- way to do jumps...)
data TmVar = TmVar String Int
  deriving (Eq, Ord)
data CoVar = CoVar String Int
  deriving (Eq, Ord)
data TyVar = TyVar String Int

instance Show TmVar where
  show (TmVar x i) = x ++ show i
instance Show CoVar where
  show (CoVar k i) = k ++ show i
instance Show TyVar where
  show (TyVar a i) = a ++ show i

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
  -- case x of k1 : s1 | k2 : s2 | ..., branch
  -- Idea: instead of annotating each covar with its 'ContK ss' , maybe
  -- annotate 'x' with its type? This would let us know what sum type we are
  -- analysing, and from that derive the type of each branch.
  -- (Sort of. If it's a data type constructor, I would still need a symbol
  -- table to look up the constructors of that type.)
  | CaseK TmVar [(CoVar, TypeK)]
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

cpsType :: S.Type -> TypeK
cpsType S.TyUnit = UnitK
cpsType S.TyInt = IntK
cpsType S.TyBool = BoolK
cpsType (S.TySum a b) = SumK (cpsType a) (cpsType b)
cpsType (S.TyProd a b) = ProdK (cpsType a) (cpsType b)
cpsType (S.TyArr argTy retTy) = ContK [cpsType argTy, ContK [cpsType retTy]]
cpsType (S.TyVarOcc _) = error "not implemented: polymorphic cpsType"
cpsType (S.TyAll _ _) = error "not implemented: polymorphic cpsType"

contDefType :: ContDef a -> TypeK
contDefType (ContDef _ _ xs _) = ContK (map snd xs)


-- TODO: Verify that correct types are being returned by 'cps'
-- (I'm confused about some things regarding the type returned by invoking the
-- continuation, etc.)
-- I fixed the most glaring issues, but I'm certain that more are lurking.

-- | CPS-convert a term.
cps :: Term -> (TmVar -> S.Type -> CPS (TermK (), S.Type)) -> CPS (TermK (), S.Type)
cps (TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> throwError (NotInScope x)
    Just (x', t) -> k x' t
cps TmNil k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyUnit
    let res = LetValK x UnitK NilK e'
    pure (res, t')
cps (TmInt i) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyInt
    let res = LetValK x IntK (IntValK i) e'
    pure (res, t')
cps (TmBool b) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyBool
    let res = LetValK x BoolK (BoolValK b) e'
    pure (res, t')
cps (TmArith e1 op e2) k =
  cps e1 $ \x t1 -> do
    assertEqual S.TyInt t1
    cps e2 $ \y t2 -> do
      assertEqual S.TyInt t2
      freshTm "z" $ \z -> do
        (e', t') <- k z S.TyInt
        let res = LetArithK z (makeArith op x y) e'
        pure (res, t')
cps (TmCmp e1 cmp e2) k =
  cps e1 $ \x t1 -> do
    assertEqual S.TyInt t1
    cps e2 $ \y t2 -> do
      assertEqual S.TyInt t2
      freshTm "z" $ \z -> do
        (e', t') <- k z S.TyBool
        let res = LetCompareK z (makeCompare cmp x y) e'
        pure (res, t')
cps (TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let ty = S.TyProd t1 t2
        (e', t') <- k x ty
        let res = LetValK x (cpsType ty) (PairK v1 v2) e'
        pure (res, t')
cps (TmInl a b e) k =
  cps e $ \z t -> do
    assertEqual a t
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      (e', t') <- k x ty
      let res = LetValK x (cpsType ty) (InlK z) e'
      pure (res, t')
cps (TmInr a b e) k =
  cps e $ \z t -> do
    assertEqual b t
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      (e', t') <- k x ty
      let res = LetValK x (cpsType ty) (InrK z) e'
      pure (res, t')
cps (TmLam x argTy e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- withVarBinds bs $ cpsTail e k'
        let s' = cpsType retTy
        let fun = FunDef () f (map (second cpsType . snd) bs) [(k', ContK [s'])] e'
        pure (fun, S.TyArr argTy retTy)
      (e'', t'') <- k f ty
      pure (LetFunK [fun] e'', t'')
cps (TmLet x t e1 e2) k = do
  freshCo "j" $ \j -> do
    (kont, t2') <- freshenVarBinds [(x, t)] $ \bs -> do
      (e2', t2') <- withVarBinds bs $ cps e2 k
      let kont = ContDef () j (map (second cpsType . snd) bs) e2'
      pure (kont, t2')
    (e1', t1') <- cpsTail e1 j
    assertEqual t t1'
    pure (LetContK [kont] e1', t2')
cps (TmRecFun fs e) k = do
  (fs', e', t') <- freshenFunBinds fs $ \binds -> do
    fs' <- withVarBinds binds $ traverse cpsFun fs
    (e', t') <- withVarBinds binds $ cps e k
    pure (fs', e', t')
  let res = LetFunK fs' e'
  pure (res, t')
cps (TmCase e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    assertEqual (S.TySum tl tr) t
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        let s' = cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z j s [([(xl, tl)], el), ([(xr, tr)], er)]
        pure (LetContK [kont] res, s)
cps (TmIf e s et ef) k =
  cps e $ \z t -> do
    assertEqual S.TyBool t
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        let s' = cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        -- NOTE: ef, et is the correct order here.
        -- This is because case branches are laid out in order of discriminant.
        -- false = 0, true = 1, so the branches should be laid
        -- out as false, true as opposed to the source order true, false.
        res <- cpsCase z j s [([], ef), ([], et)]
        pure (LetContK [kont] res, s)
cps (TmApp e1 e2) k =
  cps e1 $ \v1 t1 -> do
    cps e2 $ \v2 t2 -> do
      (argTy, retTy) <- case t1 of
        S.TyArr argTy retTy -> pure (argTy, retTy)
        _ -> throwError (CannotApply t1)
      assertEqual argTy t2
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          (e', t') <- k xv retTy
          let res = LetContK [ContDef () kv [(xv, cpsType retTy)] e'] (CallK v1 [v2] [kv])
          pure (res, t')
cps (TmFst e) k =
  cps e $ \v t ->  do
    (ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> throwError (CannotProject t)
    freshTm "x" $ \x -> do
      (e', t') <- k x ta
      let res = LetFstK x (cpsType ta) v e'
      pure (res, t')
cps (TmSnd e) k =
  cps e $ \v t -> do
    (ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> throwError (CannotProject t)
    freshTm "x" $ \x -> do
      (e', t') <- k x tb
      let res = LetSndK x (cpsType tb) v e'
      pure (res, t')

cpsFun :: TmFun -> CPS (FunDef ())
cpsFun (TmFun f x t s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable?)"
      Just (f', _) -> pure f'
    fun <- freshenVarBinds [(x, t)] $ \bs -> do
      (e', s') <- withVarBinds bs $ cpsTail e k
      assertEqual s s'
      pure (FunDef () f' (map (second cpsType . snd) bs) [(k, ContK [cpsType s])] e')
    pure fun

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Term -> CoVar -> CPS (TermK (), S.Type)
cpsTail (TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> throwError (NotInScope x)
    Just (x', t') -> pure (JumpK k [x'], t')
cpsTail (TmLam x argTy e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- withVarBinds bs $ cpsTail e k'
        let s' = cpsType retTy
        let fun = FunDef () f (map (second cpsType . snd) bs) [(k', ContK [s'])] e'
        pure (fun, S.TyArr argTy retTy)
      let res = LetFunK [fun] (JumpK k [f])
      pure (res, ty)
cpsTail (TmLet x t e1 e2) k =
  -- [[let x:t = e1 in e2]] k
  -- -->
  -- let j (x:t) = [[e2]] k; in [[e1]] j
  -- (This is similar to, but not quite the same as @case e1 of x:t -> e2@)
  freshCo "j" $ \j -> do
    (kont, t2') <- cpsBranch j [(x, t)] e2 k
    (e1', t1') <- cpsTail e1 j
    assertEqual t t1'
    pure (LetContK [kont] e1', t2')
cpsTail (TmRecFun fs e) k = do
  (fs', e', t') <- freshenFunBinds fs $ \binds -> do
    fs' <- withVarBinds binds $ traverse cpsFun fs
    (e', t') <- withVarBinds binds $ cpsTail e k
    pure (fs', e', t')
  let res = LetFunK fs' e'
  pure (res, t')
cpsTail TmNil k =
  freshTm "x" $ \x -> do
    let res = LetValK x UnitK NilK (JumpK k [x])
    pure (res, S.TyUnit)
cpsTail (TmInt i) k =
  freshTm "x" $ \x -> do
    let res = LetValK x IntK (IntValK i) (JumpK k [x])
    pure (res, S.TyInt)
cpsTail (TmBool b) k =
  freshTm "x" $ \x ->
    pure (LetValK x BoolK (BoolValK b) (JumpK k [x]), S.TyBool)
cpsTail (TmArith e1 op e2) k =
  cps e1 $ \x t1 -> do
    assertEqual S.TyInt t1
    cps e2 $ \y t2 -> do
      assertEqual S.TyInt t2
      freshTm "z" $ \z -> do
        let res = LetArithK z (makeArith op x y) (JumpK k [z])
        pure (res, S.TyInt)
cpsTail (TmCmp e1 cmp e2) k =
  cps e1 $ \x t1 -> do
    assertEqual S.TyInt t1
    cps e2 $ \y t2 -> do
      assertEqual S.TyInt t2
      freshTm "z" $ \z -> do
        let res = LetCompareK z (makeCompare cmp x y) (JumpK k [z])
        pure (res, S.TyBool)
cpsTail (TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let ty = S.TyProd t1 t2
        let res = LetValK x (cpsType ty) (PairK v1 v2) (JumpK k [x])
        pure (res, ty)
cpsTail (TmInl a b e) k =
  cps e $ \z t -> do
    assertEqual a t
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      let res = LetValK x (cpsType ty) (InlK z) (JumpK k [x])
      pure (res, ty)
cpsTail (TmInr a b e) k =
  cps e $ \z t -> do
    assertEqual b t
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      let res = LetValK x (cpsType ty) (InrK z) (JumpK k [x])
      pure (res, ty)
cpsTail (TmCase e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    assertEqual (S.TySum tl tr) t
    res <- cpsCase z k s [([(xl, tl)], el), ([(xr, tr)], er)]
    pure (res, s)
cpsTail (TmIf e s et ef) k =
  cps e $ \z t -> do
    assertEqual S.TyBool t
    -- NOTE: ef, et is the correct order here.
    -- This is because case branches are laid out in order of discriminant.
    -- false = 0, true = 1, so the branches should be laid
    -- out as false, true as oppose to the source order true,
    -- false.
    res <- cpsCase z k s [([], ef), ([], et)]
    pure (res, s)
cpsTail (TmApp e1 e2) k =
  cps e1 $ \f t1 ->
    cps e2 $ \x t2 -> do
      (argTy, retTy) <- case t1 of
        S.TyArr argTy retTy -> pure (argTy, retTy)
        _ -> throwError (CannotApply t1)
      assertEqual argTy t2
      let res = CallK f [x] [k]
      pure (res, retTy)
cpsTail (TmFst e) k =
  cps e $ \z t -> do
    (ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> throwError (CannotProject t)
    freshTm "x" $ \x -> do
      let res = LetFstK x (cpsType ta) z (JumpK k [x])
      pure (res, ta)
cpsTail (TmSnd e) k =
  cps e $ \z t -> do
    (ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> throwError (CannotProject t)
    freshTm "x" $ \x -> do
      let res = LetSndK x (cpsType tb) z (JumpK k [x])
      pure (res, tb)


cpsMain :: Term -> Either TCError (TermK (), S.Type)
cpsMain e = runExcept . flip runReaderT emptyEnv . runCPS $
  cps e (\z t -> pure (HaltK z, t))


-- | CPS-transform a case alternative @(x:t)+ -> e@.
--
-- @cpsBranch k xs e j@ returns @(cont k xs = [[e]] j;, s)@ where @s@ is the
-- type of @e@.
cpsBranch :: CoVar -> [(S.TmVar, S.Type)] -> Term -> CoVar -> CPS (ContDef (), S.Type)
cpsBranch k xs e j = freshenVarBinds xs $ \xs' -> do
  (e', s') <- withVarBinds xs' $ cpsTail e j
  pure (ContDef () k (map (second cpsType . snd) xs') e', s')

-- | CPS-transform a case analysis, given a scrutinee, a continuation variable
-- and its expected type, and a list of branches with bound variables.
cpsCase :: TmVar -> CoVar -> S.Type -> [([(S.TmVar, S.Type)], Term)] -> CPS (TermK ())
cpsCase z j s bs = do
  -- Pick names for each branch continuation
  scope <- asks cpsEnvScope
  let
    pick sc b =
      let i = fromMaybe 0 (Map.lookup "k" sc) in
      let k' = CoVar "k" i in
      (Map.insert "k" (i+1) sc, (k', b))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx) = CPSEnv sc' ctx
  -- CPS each branch
  konts <- local extend $ for bs' $ \ (k, (xs, e)) -> do
    (kont, s') <- cpsBranch k xs e j
    assertEqual s s'
    pure (k, kont)
  -- Assemble the result term
  let alts = map (second contDefType) konts
  let res = foldr (LetContK . (:[]) . snd) (CaseK z alts) konts
  pure res


data CPSEnv = CPSEnv { cpsEnvScope :: Map String Int, cpsEnvCtx :: Map S.TmVar (TmVar, S.Type) }

data TCError
  = NotInScope S.TmVar
  | TypeMismatch S.Type S.Type -- expected, actual
  | CannotProject S.Type
  | CannotApply S.Type

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    ["type mismatch:"
    ,"expected: " ++ S.pprintType 0 expected
    ,"actual:   " ++ S.pprintType 0 actual
    ]
  show (NotInScope x) = "variable not in scope: " ++ show x
  show (CannotApply t) = "value of type " ++ S.pprintType 0 t ++ " cannot have an argument applied to it"
  show (CannotProject t) = "cannot project field from value of type " ++ S.pprintType 0 t

emptyEnv :: CPSEnv
emptyEnv = CPSEnv Map.empty Map.empty

newtype CPS a = CPS { runCPS :: ReaderT CPSEnv (Except TCError) a }

deriving newtype instance Functor CPS
deriving newtype instance Applicative CPS
deriving newtype instance Monad CPS
deriving newtype instance MonadReader CPSEnv CPS
deriving newtype instance MonadError TCError CPS

assertEqual :: S.Type -> S.Type -> CPS ()
assertEqual expected actual = when (not (eqType expected actual)) $
  throwError (TypeMismatch expected actual)

-- TODO: What if instead of bool, I returned a datastructure pointing out the
-- path to the first(?) (or all) discrepancy? (Context as to why the equality failed)
-- TODO: Support polymorphic types here.
-- wat
eqType :: S.Type -> S.Type -> Bool
eqType S.TyUnit S.TyUnit = True
eqType S.TyUnit _ = False
eqType S.TyBool S.TyBool = True
eqType S.TyBool _ = False
eqType S.TyInt S.TyInt = True
eqType S.TyInt _ = False
eqType (S.TyProd t1 t2) (S.TyProd t3 t4) = eqType t1 t3 && eqType t2 t4
eqType (S.TyProd _ _) _ = False
eqType (S.TySum t1 t2) (S.TySum t3 t4) = eqType t1 t3 && eqType t2 t4
eqType (S.TySum _ _) _ = False
eqType (S.TyArr arg1 ret1) (S.TyArr arg2 ret2) = eqType arg1 arg2 && eqType ret1 ret2
eqType (S.TyArr _ _) _ = False
eqType t1 t2 = error ("not implemented: eqType " ++ S.pprintType 10 t1 ++ " " ++ S.pprintType 10 t2)

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
  let x' = CoVar x i
  let extend (CPSEnv sc ctx) = CPSEnv (Map.insert x (i+1) sc) ctx
  local extend (k x')

freshTy :: String -> (TyVar -> CPS a) -> CPS a
freshTy x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = TyVar x i
  let extend (CPSEnv sc ctx) = CPSEnv (Map.insert x (i+1) sc) ctx
  local extend (k x')

-- TODO: Fuse this function with 'freshenVarBinds' and 'freshenFunBinds', to
-- eliminate possibility of error.
withVarBinds :: [(S.TmVar, (TmVar, S.Type))] -> CPS a -> CPS a
withVarBinds binds m = local extend m
  where
    extend (CPSEnv sc ctx) = CPSEnv sc (foldr (uncurry Map.insert) ctx binds)

freshenVarBinds :: [(S.TmVar, S.Type)] -> ([(S.TmVar, (TmVar, S.Type))] -> CPS a) -> CPS a
freshenVarBinds bs k = do
  scope <- asks cpsEnvScope
  let
    pick sc (S.TmVar x, t) =
      let i = fromMaybe 0 (Map.lookup x sc) in
      let x' = TmVar x i in
      (Map.insert x (i+1) sc, (S.TmVar x, (x', t)))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx) = CPSEnv sc' ctx
  local extend (k bs')

freshenFunBinds :: [TmFun] -> ([(S.TmVar, (TmVar, S.Type))] -> CPS a) -> CPS a
freshenFunBinds fs k = do
  scope <- asks cpsEnvScope
  let
    pick :: Map String Int -> TmFun -> (Map String Int, (S.TmVar, (TmVar, S.Type)))
    pick sc (TmFun (S.TmVar f) _x argTy retTy _e) =
      let i = fromMaybe 0 (Map.lookup f scope) in
      let f' = TmVar f i in
      (Map.insert f (i+1) sc, (S.TmVar f, (f', S.TyArr argTy retTy)))
    (sc', binds) = mapAccumL pick scope fs
  let extend (CPSEnv _sc ctx) = CPSEnv sc' ctx
  local extend (k binds)


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermK a -> String
pprintTerm n (HaltK x) = indent n $ "halt " ++ show x ++ ";\n"
pprintTerm n (JumpK k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallK f xs ks) = indent n $ show f ++ " " ++ intercalate " " (map show xs ++ map show ks) ++ ";\n"
pprintTerm n (CaseK x ks) =
  let branches = intercalate " | " (map (show . fst) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
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
pprintType (ProdK t s) = pprintAType t ++ " * " ++ pprintAType s
pprintType (SumK t s) = pprintAType t ++ " + " ++ pprintAType s
pprintType IntK = "int"
pprintType UnitK = "unit"
pprintType BoolK = "bool"

pprintAType :: TypeK -> String
pprintAType IntK = "int"
pprintAType UnitK = "unit"
pprintAType BoolK = "bool"
pprintAType t = "(" ++ pprintType t ++ ")"
