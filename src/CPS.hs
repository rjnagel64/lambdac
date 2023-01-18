
module CPS
    ( cpsProgram
    , pprintProgram
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
    Just (aa', _) -> pure (TyVarOccK aa')
cpsType (S.TyAll aa k t) = freshenTyVarBinds [(aa, k)] $ \bs -> (\t' -> AllK bs [t']) <$> cpsCoType t
cpsType S.TyUnit = pure UnitK
cpsType S.TyInt = pure IntK
cpsType S.TyString = pure StringK
cpsType S.TyBool = pure BoolK
cpsType (S.TySum a b) = SumK <$> cpsType a <*> cpsType b
cpsType (S.TyProd a b) = ProdK <$> cpsType a <*> cpsType b
cpsType (S.TyArr a b) = (\a' b' -> FunK [a'] [b']) <$> cpsType a <*> cpsCoType b
cpsType (S.TyList a) = ListK <$> cpsType a
cpsType (S.TyConOcc (S.TyCon tc)) = pure (TyConOccK (TyCon tc))
cpsType (S.TyApp a b) = TyAppK <$> cpsType a <*> cpsType b

cpsCoType :: S.Type -> CPS CoTypeK
cpsCoType s = (\s' -> ContK [s']) <$> cpsType s

cpsKind :: S.Kind -> CPS KindK
cpsKind S.KiStar = pure StarK

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
cps (S.TmCtorOcc c) k = do
  env <- asks cpsEnvCtors
  case Map.lookup c env of
    Nothing -> error "scope error"
    Just (c', t) -> k c' t
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
      let res = LetArithK z (NegK x) e'
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
cps (S.TmCons s e1 e2) k =
  cps e1 $ \v1 _t1 ->
    cps e2 $ \v2 _t2 -> do
      freshTm "x" $ \x -> do
        ty' <- ListK <$> cpsType s
        (e', t') <- k x (S.TyList s)
        let res = LetValK x ty' (ConsK v1 v2) e'
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
cps (S.TmTLam aa ki e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [(aa, ki)] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let def = AbsDef () f bs [(k', s')] e'
        pure (def, S.TyAll aa ki retTy)
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
cps (S.TmCaseSum e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j [(S.Ctor "inl", [(xl, tl)], el), (S.Ctor "inr", [(xr, tr)], er)]
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
        res <- cpsCase z t j [(S.Ctor "false", [], ef), (S.Ctor "true", [], et)]
        pure (LetContK [kont] res, s)
cps (S.TmCaseList e s en ((y, thd), (ys, ttl), ec)) k =
  cps e $ \z t -> do
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j [(S.Ctor "nil", [], en), (S.Ctor "cons", [(y, thd), (ys, ttl)], ec)]
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
      S.TyAll aa _ki t1' -> pure (aa, t1')
      _ -> error "type error"
    freshCo "k" $ \kv ->
      freshTm "f" $ \fv -> do
        let instTy = S.substType (S.singleSubst aa t) t1'
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
cps (S.TmCase e s alts) k =
  cps e $ \z t ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x -> do
        s' <- cpsType s
        (e', _t') <- k x s
        let kont = ContDef () j [(x, s')] e'
        res <- cpsCase z t j alts
        pure (LetContK [kont] res, s)

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
cpsFun (S.TmTFun f aa ki s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable)"
      Just (f', _) -> pure f'
    fun <- freshenTyVarBinds [(aa, ki)] $ \bs -> do
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
cpsTail (S.TmCtorOcc c) k = do
  env <- asks cpsEnvCtors
  case Map.lookup c env of
    Nothing -> error "scope error"
    Just (c', t') -> pure (JumpK k [c'], t')
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
cpsTail (S.TmTLam aa ki e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [(aa, ki)] $ \bs -> do
        (e', retTy) <- cpsTail e k'
        s' <- cpsCoType retTy
        let def = AbsDef () f bs [(k', s')] e'
        pure (def, S.TyAll aa ki retTy)
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
cpsTail (S.TmEmpty s) k =
  freshTm "x" $ \x -> do
    s' <- ListK <$> cpsType s
    let res = LetValK x s' EmptyK (JumpK k [x])
    pure (res, S.TyList s)
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
      let res = LetArithK z (NegK x) (JumpK k [z])
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
cpsTail (S.TmCons s e1 e2) k =
  cps e1 $ \v1 _t1 ->
    cps e2 $ \v2 _t2 -> do
      freshTm "x" $ \x -> do
        ty' <- ListK <$> cpsType s
        let res = LetValK x ty' (ConsK v1 v2) (JumpK k [x])
        pure (res, S.TyList s)
cpsTail (S.TmConcat e1 e2) k =
  cps e1 $ \v1 _t1 ->
    cps e2 $ \v2 _t2 -> do
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
cpsTail (S.TmCaseSum e s (xl, tl, el) (xr, tr, er)) k =
  cps e $ \z t -> do
    res <- cpsCase z t k [(S.Ctor "inl", [(xl, tl)], el), (S.Ctor "inr", [(xr, tr)], er)]
    pure (res, s)
cpsTail (S.TmIf e s et ef) k =
  cps e $ \z t -> do
    -- NOTE: ef, et is the correct order here.
    -- This is because case branches are laid out in order of discriminant.
    -- false = 0, true = 1, so the branches should be laid
    -- out as false, true as oppose to the source order true,
    -- false.
    res <- cpsCase z t k [(S.Ctor "false", [], ef), (S.Ctor "true", [], et)]
    pure (res, s)
cpsTail (S.TmCaseList e s en ((y, thd), (ys, ttl), ec)) k =
  cps e $ \z t -> do
    res <- cpsCase z t k [(S.Ctor "nil", [], en), (S.Ctor "cons", [(y, thd), (ys, ttl)], ec)]
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
      S.TyAll aa _ki t1' -> pure (aa, t1')
      _ -> error "type error"
    let instTy = S.substType (S.singleSubst aa t) t1'
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
cpsTail (S.TmCase e s alts) k =
  cps e $ \z t -> do
    res <- cpsCase z t k alts
    pure (res, s)

-- Note: Constructor wrapper functions
--
-- Constructor applications are uncurried in every IR except source. Therefore,
-- as part of CPS, we have to adapt the curried Source IR to the uncurried CPS
-- IR. We currently do this by generating a curried "wrapper function" that
-- ultimately constructs the ctor value.
--
-- One could easily imagine a smarter translation that does not generate nearly
-- so many redundant redexes, but whatever. (e.g., enhanced CPS translation
-- that applies multiple arguments together, permit anonymous functions in CPS
-- for on-site eta-expansion instead of top-level wrappers, etc.)
--
-- Here is an example of the wrapper for a constructor
-- 'mkfoo : int -> bool -> a -> foo a b'
-- of
-- 'data foo (a ; *) (b : *)':
--
-- type is CPS[forall (a : *). forall (b : *). int -> bool -> a -> foo a b]
-- fun mkfoo (@a : *, k0 : CPS[forall (b : *). int -> bool -> a -> foo a b]) =
--   let fun w0 (@b : *, k1 : CPS[int -> bool -> a -> foo a b]) =
--     let fun w1 (arg0 : int, k2 : CPS[bool -> a -> foo a b]) =
--       let fun w2 (arg1 : bool, k3 : CPS[a -> foo a b]) =
--         let fun w3 (arg2 : a, k4 : (foo a b) -> !) =
-- 	  let c : foo a b = mkfoo(arg0, arg1, arg2) in
-- 	  k4 c
-- 	in
-- 	k3 w3
--       in
--       k2 w2
--     in
--     k1 w1
--   in
--   k0 w0
--
-- Nullary constructors (no value args, no type params) are merely let-expressions:
-- let mkbar : bar = mkbar() in ...

makeCtorWrapper :: TyCon -> [(TyVar, KindK)] -> Ctor -> [TypeK] -> TermK () -> CPS (TermK ())
makeCtorWrapper tc params c ctorargs e = do
  (w, _) <- go (let Ctor tmp = c in TmVar tmp 0) (map Left params ++ map Right ctorargs) [] e
  pure w
  where
    go :: TmVar -> [Either (TyVar, KindK) TypeK] -> [TmVar] -> TermK () -> CPS (TermK (), TypeK)
    go name [] arglist body = do
      let val = CtorAppK c arglist
      let wrapperTy = foldl (\ t (aa, _) -> TyAppK t (TyVarOccK aa)) (TyConOccK tc) params
      let wrapper = LetValK name wrapperTy val body
      pure (wrapper, wrapperTy)
    go name (Left (aa, k) : args) arglist body =
      freshTm "w" $ \newName ->
        freshCo "k" $ \newCont -> do
          (inner, innerTy) <- go newName args arglist (JumpK newCont [newName])
          let fun = AbsDef () name [(aa, k)] [(newCont, ContK [innerTy])] inner
          let wrapper = LetFunAbsK [fun] body
          pure (wrapper, AllK [(aa, k)] [ContK [innerTy]])
    go name (Right argTy : args) arglist body =
      freshTm "w" $ \newName ->
        freshTm "arg" $ \newArg ->
          freshCo "k" $ \newCont -> do
            (inner, innerTy) <- go newName args (arglist ++ [newArg]) (JumpK newCont [newName])
            let fun = FunDef () name [(newArg, argTy)] [(newCont, ContK [innerTy])] inner
            let wrapper = LetFunAbsK [fun] body
            pure (wrapper, FunK [argTy] [ContK [innerTy]])

makeDataWrapper :: DataDecl -> TermK () -> CPS (TermK ())
makeDataWrapper (DataDecl tc params ctors) e = go ctors e
  where
    go [] e' = pure e'
    go (CtorDecl c args : cs) e' = makeCtorWrapper tc params c args =<< go cs e'

addCtorWrappers :: [DataDecl] -> TermK () -> CPS (TermK ())
addCtorWrappers [] e = pure e
addCtorWrappers (dd : ds) e = makeDataWrapper dd =<< addCtorWrappers ds e

cpsDataDecl :: S.DataDecl -> CPS DataDecl
cpsDataDecl (S.DataDecl (S.TyCon tc) params ctors) = do
  freshenTyVarBinds params $ \bs -> do
    let params' = bs
    ctors' <- traverse cpsCtorDecl ctors
    pure (DataDecl (TyCon tc) params' ctors')

cpsCtorDecl :: S.CtorDecl -> CPS CtorDecl
cpsCtorDecl (S.CtorDecl (S.Ctor c) args) = CtorDecl (Ctor c) <$> traverse cpsType args

ctorWrapperBinds :: S.DataDecl -> [(S.Ctor, (TmVar, S.Type))]
ctorWrapperBinds (S.DataDecl tc params ctors) = map ctorDeclType ctors
  where
    ctorDeclType :: S.CtorDecl -> (S.Ctor, (TmVar, S.Type))
    ctorDeclType (S.CtorDecl (S.Ctor c) args) = (S.Ctor c, (TmVar c 0, ty))
      where
        ret = foldl S.TyApp (S.TyConOcc tc) (map (S.TyVarOcc . fst) params)
        ty = foldr (uncurry S.TyAll) (foldr S.TyArr ret args) params

cpsProgram :: S.Program -> Program ()
cpsProgram (S.Program ds e) = flip runReader emptyEnv . runCPS $ do
  ds' <- traverse cpsDataDecl ds

  let ctorbinds = concatMap ctorWrapperBinds ds
  let extend (CPSEnv sc tms tys cs) = CPSEnv sc tms tys (insertMany ctorbinds cs)

  -- Unfortunately, I cannot use cpsTail here because 'HaltK' is not a covar.
  -- If I manage the hybrid/fused cps transform, I should revisit this.
  (e', t) <- local extend $ cps e (\z t -> pure (HaltK z, t))
  -- let e'' = LetFunAbsK (map snd ctorWrappers) e'
  e'' <- addCtorWrappers ds' e'
  pure (Program ds' e'')


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
cpsCase :: TmVar -> S.Type -> CoVar -> [(S.Ctor, [(S.TmVar, S.Type)], S.Term)] -> CPS (TermK ())
cpsCase z t j bs = do
  -- Pick names for each branch continuation
  scope <- asks cpsEnvScope
  let
    pick sc b =
      let i = fromMaybe 0 (Map.lookup "k" sc) in
      let k' = CoVar "k" i in
      (Map.insert "k" (i+1) sc, (k', b))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx tys cs) = CPSEnv sc' ctx tys cs
  -- CPS each branch
  (ks, konts) <- fmap unzip $ local extend $ for bs' $ \ (k, (S.Ctor c, xs, e)) -> do
    (kont, _s') <- cpsBranch k xs e j
    pure ((Ctor c, k), kont)
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
  , cpsEnvTyCtx :: Map S.TyVar (TyVar, S.Kind)
  , cpsEnvCtors :: Map S.Ctor (TmVar, S.Type)
  }

emptyEnv :: CPSEnv
emptyEnv = CPSEnv Map.empty Map.empty Map.empty Map.empty

freshTm :: String -> (TmVar -> CPS a) -> CPS a
freshTm x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = TmVar x i
  let extend (CPSEnv sc ctx tys cs) = CPSEnv (Map.insert x (i+1) sc) ctx tys cs
  local extend (k x')

freshCo :: String -> (CoVar -> CPS a) -> CPS a
freshCo x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = CoVar x i
  let extend (CPSEnv sc ctx tys cs) = CPSEnv (Map.insert x (i+1) sc) ctx tys cs
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
  let extend (CPSEnv _sc ctx tys cs) = CPSEnv sc' (insertMany bs' ctx) tys cs
  bs'' <- traverse (\ (_, (x', t)) -> (,) x' <$> cpsType t) bs'
  local extend (k bs'')

freshenTyVarBinds :: [(S.TyVar, S.Kind)] -> ([(TyVar, KindK)] -> CPS a) -> CPS a
freshenTyVarBinds bs k = do
  scope <- asks cpsEnvScope
  let
    -- pick :: Map String Int -> (S.TyVar, S.Kind) -> (Map String Int, (S.TyVar, TyVar))
    pick sc (S.TyVar aa, ki) =
      let i = fromMaybe 0 (Map.lookup aa scope) in
      let aa' = TyVar aa i in
      (Map.insert aa (i+1) sc, (S.TyVar aa, (aa', ki)))
    (sc', bs') = mapAccumL pick scope bs
  let extend (CPSEnv _sc ctx tys cs) = CPSEnv sc' ctx (insertMany bs' tys) cs
  bs'' <- traverse (\ (_, (aa', k)) -> (,) aa' <$> cpsKind k) bs'
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
    pick sc (S.TmTFun (S.TmVar f) aa ki retTy _e) =
      let i = fromMaybe 0 (Map.lookup f scope) in
      let f' = TmVar f i in
      (Map.insert f (i+1) sc, (S.TmVar f, (f', S.TyAll aa ki retTy)))
    (sc', binds) = mapAccumL pick scope fs
  let extend (CPSEnv _sc ctx tys cs) = CPSEnv sc' (insertMany binds ctx) tys cs
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
  let extend (CPSEnv _sc ctx tys cs) = CPSEnv sc' (insertMany binds ctx) tys cs
  fs' <- for fs $ \ (f, ty, rhs) -> do
    case (ty, rhs) of
      (S.TyArr _t s, S.TmLam x t' body) -> do
        pure (S.TmFun f x t' s body)
      (S.TyAll aa _k1 t, S.TmTLam bb k2 body) -> do
        let sub = S.singleSubst aa (S.TyVarOcc bb)
        pure (S.TmTFun f bb k2 (S.substType sub t) body)
      (_, _) -> error "letrec error"
  local extend (k fs')


