
module CPS
    ( cpsMain
    , pprintTerm
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Traversable (mapAccumL, for)

import Control.Monad.Reader

import qualified Source as S

import CPS.IR

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


makeArith :: S.TmArith -> TmVar -> TmVar -> ArithK
makeArith S.TmArithAdd x y = AddK x y
makeArith S.TmArithSub x y = SubK x y
makeArith S.TmArithMul x y = MulK x y

makeCompare :: S.TmCmp -> TmVar -> TmVar -> CmpK
makeCompare S.TmCmpEq x y = CmpEqK x y
makeCompare S.TmCmpNe x y = CmpNeK x y
makeCompare S.TmCmpLt x y = CmpLtK x y
makeCompare S.TmCmpLe x y = CmpLeK x y
makeCompare S.TmCmpGt x y = CmpGtK x y
makeCompare S.TmCmpGe x y = CmpGeK x y

cpsType :: S.Type -> CPS TypeK
cpsType (S.TyVarOcc aa) = do
  env <- asks cpsEnvTyCtx
  case Map.lookup aa env of
    Nothing -> error "scope error"
    Just aa' -> pure (TyVarOccK aa')
cpsType (S.TyAll aa t) = freshenTyVarBinds [aa] $ \bs -> (\t' -> AllK bs [t']) <$> cpsCoType t
cpsType S.TyUnit = pure UnitK
cpsType S.TyInt = pure IntK
cpsType S.TyString = pure StringK
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
cps :: S.Term -> (TmVar -> S.Type -> CPS (TermK (), S.Type)) -> CPS (TermK (), S.Type)
cps (S.TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error "scope error"
    Just (x', t) -> k x' t
cps S.TmNil k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyUnit
    let res = LetValK x UnitK NilK e'
    pure (res, t')
cps (S.TmEmpty s) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x (S.TyList s)
    s' <- ListK <$> cpsType s
    let res = LetValK x s' EmptyK e'
    pure (res, t')
cps (S.TmInt i) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyInt
    let res = LetValK x IntK (IntValK i) e'
    pure (res, t')
cps (S.TmBool b) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyBool
    let res = LetValK x BoolK (BoolValK b) e'
    pure (res, t')
cps (S.TmString s) k =
  freshTm "x" $ \x -> do
    (e', t') <- k x S.TyString
    let res = LetValK x StringK (StringValK s) e'
    pure (res, t')
cps (S.TmArith e1 op e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        (e', t') <- k z S.TyInt
        let res = LetArithK z (makeArith op x y) e'
        pure (res, t')
cps (S.TmNegate e) k =
  cps e $ \x _t -> do
    freshTm "z" $ \z -> do
      (e', t') <- k z S.TyInt
      let res = LetNegateK z x e'
      pure (res, t')
cps (S.TmCmp e1 cmp e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        (e', t') <- k z S.TyBool
        let res = LetCompareK z (makeCompare cmp x y) e'
        pure (res, t')
cps (S.TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let ty = S.TyProd t1 t2
        (e', t') <- k x ty
        ty' <- cpsType ty
        let res = LetValK x ty' (PairK v1 v2) e'
        pure (res, t')
cps (S.TmCons e1 e2) k =
  cps e1 $ \v1 _t1 ->
    cps e2 $ \v2 t2 -> do
      freshTm "x" $ \x -> do
        (e', t') <- k x t2
        t2' <- cpsType t2
        let res = LetValK x t2' (ConsK v1 v2) e'
        pure (res, t')
cps (S.TmConcat e1 e2) k =
  cps e1 $ \v1 _t1 ->
    cps e2 $ \v2 _t2 -> do
      freshTm "x" $ \x -> do
        (e', t') <- k x S.TyString
        let res = LetConcatK x v1 v2 e'
        pure (res, t')
cps (S.TmInl a b e) k =
  cps e $ \z _t -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      (e', t') <- k x ty
      ty' <- cpsType ty
      let res = LetValK x ty' (InlK z) e'
      pure (res, t')
cps (S.TmInr a b e) k =
  cps e $ \z _t -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      (e', t') <- k x ty
      ty' <- cpsType ty
      let res = LetValK x ty' (InrK z) e'
      pure (res, t')
cps (S.TmLam x argTy e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let fun = FunDef () f bs [(k', s')] e'
        pure (fun, S.TyArr argTy retTy)
      (e'', t'') <- k f ty
      pure (LetFunAbsK [fun] e'', t'')
cps (S.TmTLam aa e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [aa] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let def = AbsDef () f bs [(k', s')] e'
        pure (def, S.TyAll aa retTy)
      (e'', t'') <- k f ty
      pure (LetFunAbsK [def] e'', t'')
cps (S.TmLet x t e1 e2) k = do
  freshCo "j" $ \j -> do
    (kont, t2') <- freshenVarBinds [(x, t)] $ \bs -> do
      (e2', t2') <- cps e2 k
      let kont = ContDef () j bs e2'
      pure (kont, t2')
    (e1', _t1') <- cpsTail e1 j
    pure (LetContK [kont] e1', t2')
cps (S.TmRecFun fs e) k = do
  (fs', e', t') <- freshenFunBinds fs $ do
    fs' <- traverse cpsFun fs
    (e', t') <- cps e k
    pure (fs', e', t')
  let res = LetFunAbsK fs' e'
  pure (res, t')
cps (S.TmLetRec fs e) k = do
  (fs'', e', t') <- freshenRecBinds fs $ \fs' -> do
    fs'' <- traverse cpsFun fs'
    (e', t') <- cps e k
    pure (fs'', e', t')
  let res = LetFunAbsK fs'' e'
  pure (res, t')
cps (S.TmCase e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j [([(xl, tl)], el), ([(xr, tr)], er)]
        pure (LetContK [kont] res, s)
cps (S.TmIf e s et ef) k =
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
cps (S.TmCaseList e s en ((y, thd), (ys, ttl), ec)) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j [([], en), ([(y, thd), (ys, ttl)], ec)]
        pure (LetContK [kont] res, s)
cps (S.TmApp e1 e2) k =
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
cps (S.TmTApp e t) k =
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
cps (S.TmFst e) k =
  cps e $ \v t ->  do
    (ta, _tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- k x ta
      ta' <- cpsType ta
      let res = LetFstK x ta' v e'
      pure (res, t')
cps (S.TmSnd e) k =
  cps e $ \v t -> do
    (_ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- k x tb
      tb' <- cpsType tb
      let res = LetSndK x tb' v e'
      pure (res, t')

cpsFun :: S.TmFun -> CPS (FunDef ())
cpsFun (S.TmFun f x t s e) =
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
cpsFun (S.TmTFun f aa s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable)"
      Just (f', _) -> pure f'
    fun <- freshenTyVarBinds [aa] $ \bs -> do
      (e', _s') <- cpsTail e k
      s' <- cpsCoType s
      pure (AbsDef () f' bs [(k, s')] e')
    pure fun

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: S.Term -> CoVar -> CPS (TermK (), S.Type)
cpsTail (S.TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error "scope error"
    Just (x', t') -> pure (JumpK k [x'], t')
cpsTail (S.TmLam x argTy e) k =
  freshTm "f" $ \ f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let fun = FunDef () f bs [(k', s')] e'
        pure (fun, S.TyArr argTy retTy)
      let res = LetFunAbsK [fun] (JumpK k [f])
      pure (res, ty)
cpsTail (S.TmTLam aa e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [aa] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let def = AbsDef () f bs [(k', s')] e'
        pure (def, S.TyAll aa retTy)
      let res = LetFunAbsK [def] (JumpK k [f])
      pure (res, ty)
cpsTail (S.TmLet x t e1 e2) k =
  -- [[let x:t = e1 in e2]] k
  -- -->
  -- let j (x:t) = [[e2]] k; in [[e1]] j
  -- (This is similar to, but not quite the same as @case e1 of x:t -> e2@)
  freshCo "j" $ \j -> do
    (kont, t2') <- cpsBranch j [(x, t)] e2 k
    (e1', _t1') <- cpsTail e1 j
    pure (LetContK [kont] e1', t2')
cpsTail (S.TmRecFun fs e) k = do
  (fs', e', t') <- freshenFunBinds fs $ do
    fs' <- traverse cpsFun fs
    (e', t') <- cpsTail e k
    pure (fs', e', t')
  let res = LetFunAbsK fs' e'
  pure (res, t')
cpsTail (S.TmLetRec fs e) k = do
  (fs'', e', t') <- freshenRecBinds fs $ \fs' -> do
    fs'' <- traverse cpsFun fs'
    (e', t') <- cpsTail e k
    pure (fs'', e', t')
  let res = LetFunAbsK fs'' e'
  pure (res, t')
cpsTail S.TmNil k =
  freshTm "x" $ \x -> do
    let res = LetValK x UnitK NilK (JumpK k [x])
    pure (res, S.TyUnit)
cpsTail (S.TmEmpty a) k =
  freshTm "x" $ \x -> do
    a' <- ListK <$> cpsType a
    let res = LetValK x a' EmptyK (JumpK k [x])
    pure (res, S.TyList a)
cpsTail (S.TmInt i) k =
  freshTm "x" $ \x -> do
    let res = LetValK x IntK (IntValK i) (JumpK k [x])
    pure (res, S.TyInt)
cpsTail (S.TmBool b) k =
  freshTm "x" $ \x ->
    pure (LetValK x BoolK (BoolValK b) (JumpK k [x]), S.TyBool)
cpsTail (S.TmString s) k =
  freshTm "x" $ \x ->
    pure (LetValK x StringK (StringValK s) (JumpK k [x]), S.TyString)
cpsTail (S.TmArith e1 op e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        let res = LetArithK z (makeArith op x y) (JumpK k [z])
        pure (res, S.TyInt)
cpsTail (S.TmNegate e) k =
  cps e $ \x _t -> do
    freshTm "z" $ \z -> do
      let res = LetNegateK z x (JumpK k [z])
      pure (res, S.TyInt)
cpsTail (S.TmCmp e1 cmp e2) k =
  cps e1 $ \x _t1 -> do
    cps e2 $ \y _t2 -> do
      freshTm "z" $ \z -> do
        let res = LetCompareK z (makeCompare cmp x y) (JumpK k [z])
        pure (res, S.TyBool)
cpsTail (S.TmPair e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 ->
      freshTm "x" $ \x -> do
        let ty = S.TyProd t1 t2
        ty' <- cpsType ty
        let res = LetValK x ty' (PairK v1 v2) (JumpK k [x])
        pure (res, ty)
cpsTail (S.TmCons e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 -> do
      freshTm "x" $ \x -> do
        t1' <- ListK <$> cpsType t1
        let res = LetValK x t1' (ConsK v1 v2) (JumpK k [x])
        pure (res, t2)
cpsTail (S.TmConcat e1 e2) k =
  cps e1 $ \v1 t1 ->
    cps e2 $ \v2 t2 -> do
      freshTm "x" $ \x -> do
        let res = LetConcatK x v1 v2 (JumpK k [x])
        pure (res, S.TyString)
cpsTail (S.TmInl a b e) k =
  cps e $ \z _ -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      ty' <- cpsType ty
      let res = LetValK x ty' (InlK z) (JumpK k [x])
      pure (res, ty)
cpsTail (S.TmInr a b e) k =
  cps e $ \z _ -> do
    freshTm "x" $ \x -> do
      let ty = S.TySum a b
      ty' <- cpsType ty
      let res = LetValK x ty' (InrK z) (JumpK k [x])
      pure (res, ty)
cpsTail (S.TmCase e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    res <- cpsCase z t k [([(xl, tl)], el), ([(xr, tr)], er)]
    pure (res, s)
cpsTail (S.TmIf e s et ef) k =
  cps e $ \z t -> do
    -- NOTE: ef, et is the correct order here.
    -- This is because case branches are laid out in order of discriminant.
    -- false = 0, true = 1, so the branches should be laid
    -- out as false, true as oppose to the source order true,
    -- false.
    res <- cpsCase z t k [([], ef), ([], et)]
    pure (res, s)
cpsTail (S.TmCaseList e s en ((y, thd), (ys, ttl), ec)) k =
  cps e $ \z t -> do
    res <- cpsCase z t k [([], en), ([(y, thd), (ys, ttl)], ec)]
    pure (res, s)
cpsTail (S.TmApp e1 e2) k =
  cps e1 $ \f t1 ->
    cps e2 $ \x _t2 -> do
      retTy <- case t1 of
        S.TyArr _argTy retTy -> pure retTy
        _ -> error "type error"
      let res = CallK f [x] [k]
      pure (res, retTy)
cpsTail (S.TmTApp e t) k =
  cps e $ \v1 t1 -> do
    (aa, t1') <- case t1 of
      S.TyAll aa t1' -> pure (aa, t1')
      _ -> error "type error"
    let instTy = S.subst aa t t1'
    t' <- cpsType t
    let res = InstK v1 [t'] [k]
    pure (res, instTy)
cpsTail (S.TmFst e) k =
  cps e $ \z t -> do
    (ta, _tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      ta' <- cpsType ta
      let res = LetFstK x ta' z (JumpK k [x])
      pure (res, ta)
cpsTail (S.TmSnd e) k =
  cps e $ \z t -> do
    (_ta, tb) <- case t of
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      tb' <- cpsType tb
      let res = LetSndK x tb' z (JumpK k [x])
      pure (res, tb)

-- | CPS-convert a source program. Returns an equivalent CPS program.
--
-- Unfortunately, even though 'e' is in tail position, I cannot use 'cpsTail'
-- This is because 'HaltK' is not a 'CoVar'.
cpsMain :: S.Term -> TermK ()
cpsMain e = fst . flip runReader emptyEnv . runCPS $
  cps e (\z t -> pure (HaltK z, t))


-- | CPS-transform a case alternative @(x:t)+ -> e@.
--
-- @cpsBranch k xs e j@ returns @(cont k xs = [[e]] j;, s)@ where @s@ is the
-- type of @e@.
cpsBranch :: CoVar -> [(S.TmVar, S.Type)] -> S.Term -> CoVar -> CPS (ContDef (), S.Type)
cpsBranch k xs e j = freshenVarBinds xs $ \xs' -> do
  (e', s') <- cpsTail e j
  pure (ContDef () k xs' e', s')

-- | CPS-transform a case analysis, given a scrutinee, a continuation variable,
-- and a list of branches with bound variables.
cpsCase :: TmVar -> S.Type -> CoVar -> [([(S.TmVar, S.Type)], S.Term)] -> CPS (TermK ())
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
freshenFunBinds :: [S.TmFun] -> CPS a -> CPS a
freshenFunBinds fs m = do
  scope <- asks cpsEnvScope
  let
    pick :: Map String Int -> S.TmFun -> (Map String Int, (S.TmVar, (TmVar, S.Type)))
    pick sc (S.TmFun (S.TmVar f) _x argTy retTy _e) =
      let i = fromMaybe 0 (Map.lookup f scope) in
      let f' = TmVar f i in
      (Map.insert f (i+1) sc, (S.TmVar f, (f', S.TyArr argTy retTy)))
    pick sc (S.TmTFun (S.TmVar f) aa retTy _e) =
      let i = fromMaybe 0 (Map.lookup f scope) in
      let f' = TmVar f i in
      (Map.insert f (i+1) sc, (S.TmVar f, (f', S.TyAll aa retTy)))
    (sc', binds) = mapAccumL pick scope fs
  let extend (CPSEnv _sc ctx tys) = CPSEnv sc' (insertMany binds ctx) tys
  local extend m

freshenRecBinds :: [(S.TmVar, S.Type, S.Term)] -> ([S.TmFun] -> CPS a) -> CPS a
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
        pure (S.TmFun f x t' s body)
      (S.TyAll aa t, S.TmTLam bb body) -> do
        pure (S.TmTFun f bb (S.subst aa (S.TyVarOcc bb) t) body)
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


