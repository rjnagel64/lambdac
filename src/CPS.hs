
module CPS
    ( TermK(..)
    , TmVar(..)
    , CoVar(..)
    , TyVar(..)
    , FunDef(..)
    , ContDef(..)
    , AbsDef(..)
    , ArithK(..)
    , CmpK(..)
    , ValueK(..)

    , TypeK(..)
    , eqTypeK
    , substTypeK
    , CoTypeK(..)
    , eqCoTypeK
    , substCoTypeK

    , cpsMain
    , pprintTerm
    , pprintType
    , pprintCoType
    , pprintValue
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Traversable (mapAccumL, for)

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


-- Interesting idea: "Revisiting the CPS Transformation and its Implementation"
-- combines 'cps' and 'cpsTail' by using a sum type as the continuation
-- argument:
-- type Cont = ObjectCont CoVar | MetaCont (TmVar -> m TermK)
-- There's also a helper function 'apply :: Cont -> TermK -> TermK'
-- This substantially deduplicates large portions of cps/cpsTail
-- I think that I could easily add a third variant 'HaltCont :: Cont' so that I
-- don't need to generate a contdef for 'halt' all the time.


-- All sorts of variables exist in the same namespace.
-- Continuations are second-class, so they get a different type. (I collapse
-- the distinction between them later on, but maybe there's a more efficient
-- way to do jumps...)
data TmVar = TmVar String Int
  deriving (Eq, Ord)
data CoVar = CoVar String Int
  deriving (Eq, Ord)
data TyVar = TyVar String Int
  deriving (Eq, Ord)

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
  -- let z = x `op` y in e
  | LetArithK TmVar ArithK (TermK a)
  -- let x = -y in e
  | LetNegateK TmVar TmVar (TermK a)
  -- let z = x `cmp` y in e 
  | LetCompareK TmVar CmpK (TermK a)

  -- let rec ks in e
  | LetContK [ContDef a] (TermK a)
  -- let rec fs in e
  | LetFunK [FunDef a] (TermK a)
  | LetAbsK [AbsDef a] (TermK a)

  -- Block terminators
  -- k x..., goto k(x...)
  | JumpK CoVar [TmVar]
  -- f x k, call f(x, k)
  | CallK TmVar [TmVar] [CoVar]
  -- case x : s of k1 | k2 | ..., branch
  | CaseK TmVar TypeK [CoVar]
  -- halt x
  | HaltK TmVar
  -- f @t k
  | InstK TmVar [TypeK] [CoVar]

-- Hmm. Idle thought:
-- (in the long run) I think I should merge FunDef and AbsDef, using a
-- telescope of parameters for both. This is partly because 'letrec'
-- expressions in 'Source' can contain mixed term and type lambdas, and partly
-- because arity raising/uncurrying may merge together mixed term and type
-- parameters.
--
-- Meanwhile, ContDef can/should have type parameters, then value parameters,
-- akin to GHC's join points.

-- | Named basic blocks
-- @k (x:τ)+ := e@
data ContDef a = ContDef a CoVar [(TmVar, TypeK)] (TermK a)

-- | Function definitions
-- @f (x:τ) (k:σ) := e@
data FunDef a = FunDef a TmVar [(TmVar, TypeK)] [(CoVar, CoTypeK)] (TermK a)

-- | Type abstraction definitions
-- @f \@a (k:σ) := e@
data AbsDef a = AbsDef a TmVar [TyVar] [(CoVar, CoTypeK)] (TermK a)

-- | Values require no evaluation.
data ValueK
  = NilK
  | PairK TmVar TmVar
  | InlK TmVar
  | InrK TmVar
  | IntValK Int
  | BoolValK Bool
  | EmptyK
  | ConsK TmVar TmVar

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
  -- (τ+) -> ((σ+) -> !)+
  | FunK [TypeK] [CoTypeK]
  -- List σ
  | ListK TypeK
  -- forall aa+. ((σ+) -> !)+
  | AllK [TyVar] [CoTypeK]
  -- aa
  | TyVarOccK TyVar

-- | A co-type is the type of a continuation.
-- @(τ+) -> !@
newtype CoTypeK = ContK [TypeK]

-- | Test two types for alpha-equality.
eqTypeK :: TypeK -> TypeK -> Bool
eqTypeK t s = eqTypeK' (Alpha 0 Map.empty Map.empty) t s

-- | Test two co-types for alpha-equality.
eqCoTypeK :: CoTypeK -> CoTypeK -> Bool
eqCoTypeK t s = eqCoTypeK' (Alpha 0 Map.empty Map.empty) t s

eqTypeK' :: Alpha -> TypeK -> TypeK -> Bool
eqTypeK' sc (TyVarOccK aa) (TyVarOccK bb) = varAlpha aa bb sc
eqTypeK' _ (TyVarOccK _) _ = False
eqTypeK' sc (AllK aas ts) (AllK bbs ss) = case bindAlpha aas bbs sc of
  Nothing -> False
  Just sc' -> allEqual (eqCoTypeK' sc') ts ss
eqTypeK' _ (AllK _ _) _ = False
eqTypeK' _ UnitK UnitK = True
eqTypeK' _ UnitK _ = False
eqTypeK' _ IntK IntK = True
eqTypeK' _ IntK _ = False
eqTypeK' _ BoolK BoolK = True
eqTypeK' _ BoolK _ = False
eqTypeK' sc (ProdK t1 s1) (ProdK t2 s2) = eqTypeK' sc t1 t2 && eqTypeK' sc s1 s2
eqTypeK' _ (ProdK _ _) _ = False
eqTypeK' sc (SumK t1 s1) (SumK t2 s2) = eqTypeK' sc t1 t2 && eqTypeK' sc s1 s2
eqTypeK' _ (SumK _ _) _ = False
eqTypeK' sc (ListK t1) (ListK t2) = eqTypeK' sc t1 t2
eqTypeK' _ (ListK _) _ = False
eqTypeK' sc (FunK ts1 ss1) (FunK ts2 ss2) =
  allEqual (eqTypeK' sc) ts1 ts2 && allEqual (eqCoTypeK' sc) ss1 ss2
eqTypeK' _ (FunK _ _) _ = False

eqCoTypeK' :: Alpha -> CoTypeK -> CoTypeK -> Bool
eqCoTypeK' sc (ContK ts) (ContK ss) = allEqual (eqTypeK' sc) ts ss

data Alpha = Alpha Int (Map TyVar Int) (Map TyVar Int)

bindAlpha :: [TyVar] -> [TyVar] -> Alpha -> Maybe Alpha
bindAlpha aas bbs sc = go aas bbs sc
  where
    go [] [] sc' = Just sc'
    go (aa:aas') (bb:bbs') sc' = go aas' bbs' (bind aa bb sc')
    go _ _ _ = Nothing

    bind :: TyVar -> TyVar -> Alpha -> Alpha
    bind aa bb (Alpha l ls rs) = Alpha (l+1) (Map.insert aa l ls) (Map.insert bb l rs)

varAlpha :: TyVar -> TyVar -> Alpha -> Bool
varAlpha aa bb (Alpha _ ls rs) = case (Map.lookup aa ls, Map.lookup bb rs) of
  (Just la, Just lb) -> la == lb
  (Nothing, Nothing) -> aa == bb
  _ -> False

-- Hmm. This might be 'Eq1.liftEq' in disguise
allEqual :: (a -> a -> Bool) -> [a] -> [a] -> Bool
allEqual _ [] [] = True
allEqual eq (x:xs) (y:ys) = eq x y && allEqual eq xs ys
allEqual _ _ _ = False


-- | Compute the free type variables of a type.
typeFV :: TypeK -> Set TyVar
typeFV (TyVarOccK aa) = Set.singleton aa
typeFV (AllK aas ss) = Set.unions (map coTypeFV ss) Set.\\ Set.fromList aas
typeFV (FunK ts ss) = Set.unions (map typeFV ts) <> Set.unions (map coTypeFV ss)
typeFV (ProdK t s) = typeFV t <> typeFV s
typeFV (SumK t s) = typeFV t <> typeFV s
typeFV (ListK t) = typeFV t
typeFV UnitK = Set.empty
typeFV IntK = Set.empty
typeFV BoolK = Set.empty

-- | Compute the free type variables of a co-type.
coTypeFV :: CoTypeK -> Set TyVar
coTypeFV (ContK ts) = Set.unions (map typeFV ts)


-- | Apply a substitution to a type.
substTypeK :: [(TyVar, TypeK)] -> TypeK -> TypeK
substTypeK sub t = substTypeK' (Subst (Map.fromList sub) (typeFV t)) t

-- | Apply a substitution to a co-type.
substCoTypeK :: [(TyVar, TypeK)] -> CoTypeK -> CoTypeK
substCoTypeK sub t = substCoTypeK' (Subst (Map.fromList sub) (coTypeFV t)) t

substTypeK' :: Subst -> TypeK -> TypeK
substTypeK' sub (TyVarOccK aa) = substVar sub aa
substTypeK' sub (AllK aas ss) =
  let (aas', sub') = bindSubst aas sub in
  AllK aas' (map (substCoTypeK' sub') ss)
substTypeK' sub (FunK ts ss) = FunK (map (substTypeK' sub) ts) (map (substCoTypeK' sub) ss)
substTypeK' sub (ProdK t s) = ProdK (substTypeK' sub t) (substTypeK' sub s)
substTypeK' sub (SumK t s) = SumK (substTypeK' sub t) (substTypeK' sub s)
substTypeK' sub (ListK t) = ListK (substTypeK' sub t)
substTypeK' _ UnitK = UnitK
substTypeK' _ IntK = IntK
substTypeK' _ BoolK = BoolK

substCoTypeK' :: Subst -> CoTypeK -> CoTypeK
substCoTypeK' sub (ContK ss) = ContK (map (substTypeK' sub) ss)

data Subst = Subst (Map TyVar TypeK) (Set TyVar)

substVar :: Subst -> TyVar -> TypeK
substVar (Subst sub _) aa = case Map.lookup aa sub of
  Nothing -> TyVarOccK aa
  Just t -> t

bindSubst :: [TyVar] -> Subst -> ([TyVar], Subst)
bindSubst aas sub = (aas', sub')
  where
    (sub', aas') = mapAccumL bindOne sub aas

    bindOne :: Subst -> TyVar -> (Subst, TyVar)
    bindOne (Subst s sc) aa =
      if Set.member aa sc then
        let aa' = freshen sc aa in
        (Subst (Map.insert aa (TyVarOccK aa') s) (Set.insert aa' sc), aa')
      else
        (Subst s (Set.insert aa sc), aa)

    freshen :: Set TyVar -> TyVar -> TyVar
    freshen sc (TyVar aa i) =
      -- 'freshen' is only called when 'aa' shadows something in scope, so we
      -- always need to increment at least once.
      let aa' = TyVar aa (i+1) in
      if Set.member aa' sc then freshen sc aa' else aa'



cpsType :: S.Type -> CPS TypeK
cpsType (S.TyVarOcc aa) = do
  env <- asks cpsEnvTyCtx
  case Map.lookup aa env of
    Nothing -> error "scope error"
    Just aa' -> pure (TyVarOccK aa')
cpsType (S.TyAll aa t) = freshenTyVarBinds [aa] $ \bs -> (\t' -> AllK bs [t']) <$> cpsCoType t
cpsType S.TyUnit = pure UnitK
cpsType S.TyInt = pure IntK
cpsType S.TyBool = pure BoolK
cpsType (S.TySum a b) = SumK <$> cpsType a <*> cpsType b
cpsType (S.TyProd a b) = ProdK <$> cpsType a <*> cpsType b
cpsType (S.TyArr a b) = (\a' b' -> FunK [a'] [b']) <$> cpsType a <*> cpsCoType b
cpsType (S.TyList a) = ListK <$> cpsType a

cpsCoType :: S.Type -> CPS CoTypeK
cpsCoType s = (\s' -> ContK [s']) <$> cpsType s

-- Note: Failure modes of CPS
-- Before CPS, the source program is type-checked. This also checks that all
-- variables are properly scoped, and that letrec bindings have a lambda form
-- as the RHS.
--
-- Therefore, it is redundant to try to detect and report such errors here.
-- However, CPS does need to extract type information, which may fail.
--
-- Thus, such cases should be reported using `error` to halt the program, not
-- `throwError`.

-- | CPS-convert a term.
-- Note: The types being passed to the continuation and returned overall are a
-- bit confusing to me. It would be nice if I could write a precise
-- (dependently-typed) type signature, just as a form of documentation.
--
-- IIRC, the (TermK (), S.Type) returned here does not have the same meaning as
-- the (TermK (), S.Type) returned by cpsTail.
cps :: Term -> (TmVar -> S.Type -> CPS (TermK (), S.Type)) -> CPS (TermK (), S.Type)
cps (TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error "scope error"
    Just (x', t) -> k x' t
cps TmNil k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyUnit
    let res = LetValK x UnitK NilK e'
    pure (res, t')
cps (TmEmpty s) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x (S.TyList s)
    s' <- ListK <$> cpsType s
    let res = LetValK x s' EmptyK e'
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
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        (e', t') <- k z S.TyInt
        let res = LetArithK z (makeArith op x y) e'
        pure (res, t')
cps (TmNegate e) k =
  cps e $ \x _t -> do
    freshTm "z" $ \z -> do
      (e', t') <- k z S.TyInt
      let res = LetNegateK z x e'
      pure (res, t')
cps (TmCmp e1 cmp e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
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
        ty' <- cpsType ty
        let res = LetValK x ty' (PairK v1 v2) e'
        pure (res, t')
cps (TmCons e1 e2) k =
  cps e1 $ \v1 _t1 ->
    cps e2 $ \v2 t2 -> do
      freshTm "x" $ \x -> do
        (e', t') <- k x t2
        t2' <- cpsType t2
        let res = LetValK x t2' (ConsK v1 v2) e'
        pure (res, t')
cps (TmInl a b e) k =
  cps e $ \z _t -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      (e', t') <- k x ty
      ty' <- cpsType ty
      let res = LetValK x ty' (InlK z) e'
      pure (res, t')
cps (TmInr a b e) k =
  cps e $ \z _t -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      (e', t') <- k x ty
      ty' <- cpsType ty
      let res = LetValK x ty' (InrK z) e'
      pure (res, t')
cps (TmLam x argTy e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let fun = FunDef () f bs [(k', s')] e'
        pure (fun, S.TyArr argTy retTy)
      (e'', t'') <- k f ty
      pure (LetFunK [fun] e'', t'')
cps (TmTLam aa e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [aa] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let def = AbsDef () f bs [(k', s')] e'
        pure (def, S.TyAll aa retTy)
      (e'', t'') <- k f ty
      pure (LetAbsK [def] e'', t'')
cps (TmLet x t e1 e2) k = do
  freshCo "j" $ \j -> do
    (kont, t2') <- freshenVarBinds [(x, t)] $ \bs -> do
      (e2', t2') <- cps e2 k
      let kont = ContDef () j bs e2'
      pure (kont, t2')
    (e1', _t1') <- cpsTail e1 j
    pure (LetContK [kont] e1', t2')
cps (TmRecFun fs e) k = do
  (fs', e', t') <- freshenFunBinds fs $ do
    fs' <- traverse cpsFun fs
    (e', t') <- cps e k
    pure (fs', e', t')
  let res = LetFunK fs' e'
  pure (res, t')
cps (TmLetRec fs e) k = do
  (fs'', e', t') <- freshenRecBinds fs $ \fs' -> do
    fs'' <- traverse cpsFun fs'
    (e', t') <- cps e k
    pure (fs'', e', t')
  let res = LetFunK fs'' e'
  pure (res, t')
cps (TmCase e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j [([(xl, tl)], el), ([(xr, tr)], er)]
        pure (LetContK [kont] res, s)
cps (TmIf e s et ef) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        -- NOTE: ef, et is the correct order here.
        -- This is because case branches are laid out in order of discriminant.
        -- false = 0, true = 1, so the branches should be laid
        -- out as false, true as opposed to the source order true, false.
        res <- cpsCase z t j [([], ef), ([], et)]
        pure (LetContK [kont] res, s)
cps (TmCaseList e s en ((y, thd), (ys, ttl), ec)) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j [([], en), ([(y, thd), (ys, ttl)], ec)]
        pure (LetContK [kont] res, s)
cps (TmApp e1 e2) k =
  cps e1 $ \v1 t1 -> do
    cps e2 $ \v2 _t2 -> do
      retTy <- case t1 of
        S.TyArr _argTy retTy -> pure retTy
        _ -> error "type error"
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          (e', t') <- k xv retTy
          retTy' <- cpsType retTy
          let res = LetContK [ContDef () kv [(xv, retTy')] e'] (CallK v1 [v2] [kv])
          pure (res, t')
cps (TmTApp e t) k =
  cps e $ \v1 t1 -> do
    (aa, t1') <- case t1 of
      S.TyAll aa t1' -> pure (aa, t1')
      _ -> error "type error"
    freshCo "k" $ \kv ->
      freshTm "f" $ \fv -> do
        let instTy = S.subst aa t t1'
        (e'', t'') <- k fv instTy
        instTy' <- cpsType instTy
        t' <- cpsType t
        let res = LetContK [ContDef () kv [(fv, instTy')] e''] (InstK v1 [t'] [kv])
        pure (res, t'')
cps (TmFst e) k =
  cps e $ \v t ->  do
    (ta, _tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- k x ta
      ta' <- cpsType ta
      let res = LetFstK x ta' v e'
      pure (res, t')
cps (TmSnd e) k =
  cps e $ \v t -> do
    (_ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- k x tb
      tb' <- cpsType tb
      let res = LetSndK x tb' v e'
      pure (res, t')

cpsFun :: TmFun -> CPS (FunDef ())
cpsFun (TmFun f x t s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable)"
      Just (f', _) -> pure f'
    fun <- freshenVarBinds [(x, t)] $ \bs -> do
      (e', _s') <- cpsTail e k
      s' <- cpsCoType s
      pure (FunDef () f' bs [(k, s')] e')
    pure fun

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Term -> CoVar -> CPS (TermK (), S.Type)
cpsTail (TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error "scope error"
    Just (x', t') -> pure (JumpK k [x'], t')
cpsTail (TmLam x argTy e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let fun = FunDef () f bs [(k', s')] e'
        pure (fun, S.TyArr argTy retTy)
      let res = LetFunK [fun] (JumpK k [f])
      pure (res, ty)
cpsTail (TmTLam aa e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [aa] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let def = AbsDef () f bs [(k', s')] e'
        pure (def, S.TyAll aa retTy)
      let res = LetAbsK [def] (JumpK k [f])
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
  (fs', e', t') <- freshenFunBinds fs $ do
    fs' <- traverse cpsFun fs
    (e', t') <- cpsTail e k
    pure (fs', e', t')
  let res = LetFunK fs' e'
  pure (res, t')
cpsTail (TmLetRec fs e) k = do
  (fs'', e', t') <- freshenRecBinds fs $ \fs' -> do
    fs'' <- traverse cpsFun fs'
    (e', t') <- cpsTail e k
    pure (fs'', e', t')
  let res = LetFunK fs'' e'
  pure (res, t')
cpsTail TmNil k =
  freshTm "x" $ \x -> do
    let res = LetValK x UnitK NilK (JumpK k [x])
    pure (res, S.TyUnit)
cpsTail (TmEmpty a) k =
  freshTm "x" $ \x -> do
    a' <- ListK <$> cpsType a
    let res = LetValK x a' EmptyK (JumpK k [x])
    pure (res, S.TyList a)
cpsTail (TmInt i) k =
  freshTm "x" $ \x -> do
    let res = LetValK x IntK (IntValK i) (JumpK k [x])
    pure (res, S.TyInt)
cpsTail (TmBool b) k =
  freshTm "x" $ \x ->
    pure (LetValK x BoolK (BoolValK b) (JumpK k [x]), S.TyBool)
cpsTail (TmArith e1 op e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        let res = LetArithK z (makeArith op x y) (JumpK k [z])
        pure (res, S.TyInt)
cpsTail (TmNegate e) k =
  cps e $ \x _t -> do
    freshTm "z" $ \z -> do
      let res = LetNegateK z x (JumpK k [z])
      pure (res, S.TyInt)
cpsTail (TmCmp e1 cmp e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        let res = LetCompareK z (makeCompare cmp x y) (JumpK k [z])
        pure (res, S.TyBool)
cpsTail (TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let ty = S.TyProd t1 t2
        ty' <- cpsType ty
        let res = LetValK x ty' (PairK v1 v2) (JumpK k [x])
        pure (res, ty)
cpsTail (TmCons e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 -> do
      freshTm "x" $ \x -> do
        t1' <- ListK <$> cpsType t1
        let res = LetValK x t1' (ConsK v1 v2) (JumpK k [x])
        pure (res, t2)
cpsTail (TmInl a b e) k =
  cps e $ \z _ -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      ty' <- cpsType ty
      let res = LetValK x ty' (InlK z) (JumpK k [x])
      pure (res, ty)
cpsTail (TmInr a b e) k =
  cps e $ \z _ -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      ty' <- cpsType ty
      let res = LetValK x ty' (InrK z) (JumpK k [x])
      pure (res, ty)
cpsTail (TmCase e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    res <- cpsCase z t k [([(xl, tl)], el), ([(xr, tr)], er)]
    pure (res, s)
cpsTail (TmIf e s et ef) k =
  cps e $ \z t -> do
    -- NOTE: ef, et is the correct order here.
    -- This is because case branches are laid out in order of discriminant.
    -- false = 0, true = 1, so the branches should be laid
    -- out as false, true as oppose to the source order true,
    -- false.
    res <- cpsCase z t k [([], ef), ([], et)]
    pure (res, s)
cpsTail (TmCaseList e s en ((y, thd), (ys, ttl), ec)) k =
  cps e $ \z t -> do
    res <- cpsCase z t k [([], en), ([(y, thd), (ys, ttl)], ec)]
    pure (res, s)
cpsTail (TmApp e1 e2) k =
  cps e1 $ \f t1 ->
    cps e2 $ \x _t2 -> do
      retTy <- case t1 of
        S.TyArr _argTy retTy -> pure retTy
        _ -> error "type error"
      let res = CallK f [x] [k]
      pure (res, retTy)
cpsTail (TmTApp e t) k =
  cps e $ \v1 t1 -> do
    (aa, t1') <- case t1 of
      S.TyAll aa t1' -> pure (aa, t1')
      _ -> error "type error"
    let instTy = S.subst aa t t1'
    t' <- cpsType t
    let res = InstK v1 [t'] [k]
    pure (res, instTy)
cpsTail (TmFst e) k =
  cps e $ \z t -> do
    (ta, _tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      ta' <- cpsType ta
      let res = LetFstK x ta' z (JumpK k [x])
      pure (res, ta)
cpsTail (TmSnd e) k =
  cps e $ \z t -> do
    (_ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      tb' <- cpsType tb
      let res = LetSndK x tb' z (JumpK k [x])
      pure (res, tb)

-- | CPS-convert a source program. Returns an equivalent CPS program, and the
-- source type of the program.
--
-- Unfortunately, even though 'e' is in tail position, I cannot use 'cpsTail'
-- This is because 'HaltK' is not a 'CoVar'.
cpsMain :: Term -> (TermK (), S.Type)
cpsMain e = flip runReader emptyEnv . runCPS $
  cps e (\z t -> pure (HaltK z, t))


-- | CPS-transform a case alternative @(x:t)+ -> e@.
--
-- @cpsBranch k xs e j@ returns @(cont k xs = [[e]] j;, s)@ where @s@ is the
-- type of @e@.
cpsBranch :: CoVar -> [(S.TmVar, S.Type)] -> Term -> CoVar -> CPS (ContDef (), S.Type)
cpsBranch k xs e j = freshenVarBinds xs $ \xs' -> do
  (e', s') <- cpsTail e j
  pure (ContDef () k xs' e', s')

-- | CPS-transform a case analysis, given a scrutinee, a continuation variable,
-- and a list of branches with bound variables.
cpsCase :: TmVar -> S.Type -> CoVar -> [([(S.TmVar, S.Type)], Term)] -> CPS (TermK ())
cpsCase z t j bs = do
  -- Pick names for each branch continuation
  scope <- asks cpsEnvScope
  let
    pick sc b =
      let i = fromMaybe 0 (Map.lookup "k" sc) in
      let k' = CoVar "k" i in
      (Map.insert "k" (i+1) sc, (k', b))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx tys) = CPSEnv sc' ctx tys
  -- CPS each branch
  (ks, konts) <- fmap unzip $ local extend $ for bs' $ \ (k, (xs, e)) -> do
    (kont, _s') <- cpsBranch k xs e j
    pure (k, kont)
  -- Assemble the result term
  t' <- cpsType t
  let res = foldr (LetContK . (:[])) (CaseK z t' ks) konts
  pure res


newtype CPS a = CPS { runCPS :: Reader CPSEnv a }

deriving newtype instance Functor CPS
deriving newtype instance Applicative CPS
deriving newtype instance Monad CPS
deriving newtype instance MonadReader CPSEnv CPS

data CPSEnv
  = CPSEnv {
    cpsEnvScope :: Map String Int
  , cpsEnvCtx :: Map S.TmVar (TmVar, S.Type)
  , cpsEnvTyCtx :: Map S.TyVar TyVar
  }

emptyEnv :: CPSEnv
emptyEnv = CPSEnv Map.empty Map.empty Map.empty

freshTm :: String -> (TmVar -> CPS a) -> CPS a
freshTm x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = TmVar x i
  let extend (CPSEnv sc ctx tys) = CPSEnv (Map.insert x (i+1) sc) ctx tys
  local extend (k x')

freshCo :: String -> (CoVar -> CPS a) -> CPS a
freshCo x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = CoVar x i
  let extend (CPSEnv sc ctx tys) = CPSEnv (Map.insert x (i+1) sc) ctx tys
  local extend (k x')

insertMany :: Ord k => [(k, v)] -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

-- | Rename a sequence of variable bindings and bring them in to scope.
freshenVarBinds :: [(S.TmVar, S.Type)] -> ([(TmVar, TypeK)] -> CPS a) -> CPS a
freshenVarBinds bs k = do
  scope <- asks cpsEnvScope
  let
    pick sc (S.TmVar x, t) =
      let i = fromMaybe 0 (Map.lookup x sc) in
      let x' = TmVar x i in
      (Map.insert x (i+1) sc, (S.TmVar x, (x', t)))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx tys) = CPSEnv sc' (insertMany bs' ctx) tys
  bs'' <- traverse (\ (_, (x', t)) -> (,) x' <$> cpsType t) bs'
  local extend (k bs'')

-- | Rename a sequence of function bindings and bring them in to scope.
freshenFunBinds :: [TmFun] -> CPS a -> CPS a
freshenFunBinds fs m = do
  scope <- asks cpsEnvScope
  let
    pick :: Map String Int -> TmFun -> (Map String Int, (S.TmVar, (TmVar, S.Type)))
    pick sc (TmFun (S.TmVar f) _x argTy retTy _e) =
      let i = fromMaybe 0 (Map.lookup f scope) in
      let f' = TmVar f i in
      (Map.insert f (i+1) sc, (S.TmVar f, (f', S.TyArr argTy retTy)))
    (sc', binds) = mapAccumL pick scope fs
  let extend (CPSEnv _sc ctx tys) = CPSEnv sc' (insertMany binds ctx) tys
  local extend m

freshenRecBinds :: [(S.TmVar, S.Type, S.Term)] -> ([TmFun] -> CPS a) -> CPS a
freshenRecBinds fs k = do
  scope <- asks cpsEnvScope
  let
    pick :: Map String Int -> (S.TmVar, S.Type, S.Term) -> (Map String Int, (S.TmVar, (TmVar, S.Type)))
    pick sc (S.TmVar f, ty, _e) =
      let i = fromMaybe 0 (Map.lookup f scope) in
      let f' = TmVar f i in
      (Map.insert f (i+1) sc, (S.TmVar f, (f', ty)))
    (sc', binds) = mapAccumL pick scope fs
  let extend (CPSEnv _sc ctx tys) = CPSEnv sc' (insertMany binds ctx) tys
  fs' <- for fs $ \ (f, ty, rhs) -> do
    case (ty, rhs) of
      (S.TyArr _t s, S.TmLam x t' body) -> do
        pure (TmFun f x t' s body)
      (_, _) -> error "letrec error"
  local extend (k fs')

freshenTyVarBinds :: [S.TyVar] -> ([TyVar] -> CPS a) -> CPS a
freshenTyVarBinds bs k = do
  scope <- asks cpsEnvScope
  let
    pick :: Map String Int -> S.TyVar -> (Map String Int, (S.TyVar, TyVar))
    pick sc (S.TyVar aa) =
      let i = fromMaybe 0 (Map.lookup aa scope) in
      let aa' = TyVar aa i in
      (Map.insert aa (i+1) sc, (S.TyVar aa, aa'))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx tys) = CPSEnv sc' ctx (insertMany bs' tys)
  let bs'' = map snd bs'
  local extend (k bs'')


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermK a -> String
pprintTerm n (HaltK x) = indent n $ "halt " ++ show x ++ ";\n"
pprintTerm n (JumpK k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallK f xs ks) =
  indent n $ show f ++ " " ++ intercalate " " (map show xs ++ map show ks) ++ ";\n"
pprintTerm n (InstK f ts ks) =
  indent n $ intercalate " @" (show f : map pprintType ts) ++ " " ++ intercalate " " (map show ks) ++ ";\n"
pprintTerm n (CaseK x t ks) =
  let branches = intercalate " | " (map show ks) in
  indent n $ "case " ++ show x ++ " : " ++ pprintType t  ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetValK x t v e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFunK fs e) =
  indent n "letfun\n" ++ concatMap (pprintFunDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContK ks e) =
  indent n "letcont\n" ++ concatMap (pprintContDef (n+2)) ks ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetAbsK fs e) =
  indent n "letabs\n" ++ concatMap (pprintAbsDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetFstK x t y e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndK x t y e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetArithK x op e) =
  indent n ("let " ++ show x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetNegateK x y e) =
  indent n ("let " ++ show x ++ " = -" ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareK x cmp e) =
  indent n ("let " ++ show x ++ " = " ++ pprintCompare cmp ++ ";\n") ++ pprintTerm n e

pprintValue :: ValueK -> String
pprintValue NilK = "()"
pprintValue (PairK x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntValK i) = show i
pprintValue (BoolValK b) = if b then "true" else "false"
pprintValue (InlK x) = "inl " ++ show x
pprintValue (InrK y) = "inr " ++ show y
pprintValue EmptyK = "nil"
pprintValue (ConsK x y) = "cons " ++ show x ++ " " ++ show y

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
    pprintCoParam (k, s) = show k ++ " : " ++ pprintCoType s

pprintContDef :: Int -> ContDef a -> String
pprintContDef n (ContDef _ k xs e) =
  indent n (show k ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " (map pprintTmParam xs) ++ ")"
    pprintTmParam :: (TmVar, TypeK) -> String
    pprintTmParam (x, t) = show x ++ " : " ++ pprintType t

pprintAbsDef :: Int -> AbsDef a -> String
pprintAbsDef n (AbsDef _ f as ks e) =
  indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    -- One parameter list or two?
    params = "(" ++ intercalate ", " (map pprintTyParam as ++ map pprintCoParam ks) ++ ")"
    pprintTyParam aa = "@" ++ show aa
    pprintCoParam (k, s) = show k ++ " : " ++ pprintCoType s

pprintType :: TypeK -> String
pprintType (ProdK t s) = pprintAType t ++ " * " ++ pprintAType s
pprintType (SumK t s) = pprintAType t ++ " + " ++ pprintAType s
pprintType (ListK t) = "list " ++ pprintAType t
pprintType (FunK ts ss) =
  "(" ++ intercalate ", " tmParams ++ ") -> (" ++ intercalate ", " coParams ++ ")"
  where
    tmParams = map pprintType ts
    coParams = map pprintCoType ss
pprintType IntK = "int"
pprintType UnitK = "unit"
pprintType BoolK = "bool"
pprintType (TyVarOccK aa) = show aa
pprintType (AllK aas ss) =
  "forall " ++ intercalate " " (map show aas) ++ ". (" ++ intercalate ", " (map pprintCoType ss) ++ ") -> 0"

pprintAType :: TypeK -> String
pprintAType (TyVarOccK aa) = show aa
pprintAType IntK = "int"
pprintAType UnitK = "unit"
pprintAType BoolK = "bool"
pprintAType t = "(" ++ pprintType t ++ ")"

pprintCoType :: CoTypeK -> String
pprintCoType (ContK ss) = "(" ++ intercalate ", " (map pprintType ss) ++ ") -> 0"
