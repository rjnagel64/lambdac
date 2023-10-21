
module CPS
    ( cpsProgram
    , pprintProgram
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Traversable (mapAccumL, for)

import Control.Monad.Reader

import qualified Core.IR as S

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


makeArith :: S.TmArith -> ValueK -> ValueK -> ArithK
makeArith S.TmArithAdd x y = AddK x y
makeArith S.TmArithSub x y = SubK x y
makeArith S.TmArithMul x y = MulK x y

makeCompare :: S.TmCmp -> ValueK -> ValueK -> CmpK
makeCompare S.TmCmpEq x y = CmpEqK x y
makeCompare S.TmCmpNe x y = CmpNeK x y
makeCompare S.TmCmpLt x y = CmpLtK x y
makeCompare S.TmCmpLe x y = CmpLeK x y
makeCompare S.TmCmpGt x y = CmpGtK x y
makeCompare S.TmCmpGe x y = CmpGeK x y
makeCompare S.TmCmpEqChar x y = CmpEqCharK x y

makeStringOp :: S.TmStringOp -> ValueK -> ValueK -> (StringOpK, S.Type)
makeStringOp S.TmConcat x y = (ConcatK x y, S.TyString)
makeStringOp S.TmIndexStr x y = (IndexK x y, S.TyChar)

-- | Push a type alias at the outermost level out of the way, by substituting
-- it into the body.
push :: S.Type -> CPS S.Type
push (S.TyAliasApp al args) = do
  S.AliasDef params _k t <- lookupAlias al
  let sub = S.makeSubst [(aa, s) | ((aa, _), s) <- zip params args]
  push (S.substType sub t)
push t = pure t

lookupAlias :: S.Alias -> CPS S.AliasDef
lookupAlias al = do
  env <- asks cpsEnvAliases
  case Map.lookup al env of
    Nothing -> error "scope error"
    Just ad -> pure ad

cpsType :: S.Type -> CPS TypeK
cpsType (S.TyVarOcc aa) = do
  env <- asks cpsEnvTyCtx
  case Map.lookup aa env of
    Nothing -> error "scope error" 
    Just (aa', _) -> pure (TyVarOccK aa')
cpsType (S.TyAll aa k t) =
  freshenTyVarBinds [(aa, k)] $ \bs ->
    (\t' -> FunK (map (uncurry TypeTele) bs) [t']) <$> cpsCoType t
cpsType S.TyUnit = pure UnitK
cpsType S.TyInt = pure IntK
cpsType S.TyString = pure StringK
cpsType S.TyChar = pure CharK
cpsType S.TyBool = pure BoolK
cpsType (S.TyProd a b) = ProdK <$> cpsType a <*> cpsType b
cpsType (S.TyRecord fields) = RecordK <$> traverse cpsFieldType fields
  where cpsFieldType (S.FieldLabel f, t) = (,) <$> pure (FieldLabel f) <*> cpsType t
cpsType (S.TyArr a b) = (\a' b' -> FunK [ValueTele a'] [b']) <$> cpsType a <*> cpsCoType b
cpsType (S.TyConOcc (S.TyCon tc)) = pure (TyConOccK (TyCon tc))
cpsType (S.TyApp a b) = TyAppK <$> cpsType a <*> cpsType b
cpsType (S.TyIO a) = (\a' -> FunK [ValueTele TokenK] [ContK [TokenK, a']]) <$> cpsType a
cpsType (S.TyAliasApp al args) = do
  S.AliasDef params _k t <- lookupAlias al
  -- We assume that the input is well-formed, so length params == length args
  -- and all kinds match.
  let sub = S.makeSubst [(aa, s) | ((aa, _k), s) <- zip params args]
  cpsType (S.substType sub t)

cpsCoType :: S.Type -> CPS CoTypeK
cpsCoType s = (\s' -> ContK [s']) <$> cpsType s

cpsKind :: S.Kind -> CPS KindK
cpsKind S.KiStar = pure StarK
cpsKind (S.KiArr k1 k2) = KArrK <$> cpsKind k1 <*> cpsKind k2

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

-- | Translate an entire program to continuation-passing style.
cpsProgram :: S.Program -> Program
cpsProgram (S.Program ds e) = flip runReader emptyEnv . runCPS $ do
  ds' <- traverse cpsDataDecl ds

  let ctorbinds = concatMap ctorWrapperBinds ds
  let extend env = env { cpsEnvCtors = insertMany ctorbinds (cpsEnvCtors env) }

  -- Unfortunately, I cannot use ObjCont here because 'HaltK' is not a covar.
  -- If I manage the hybrid/fused cps transform, I should revisit this.
  (e', _t) <- local extend $ cps e (MetaCont $ \z t -> pure (HaltK z, t))
  e'' <- addCtorWrappers ds' e'
  pure (Program ds' e'')


-- | A continuation specifies what to do with the result of evaluating an
-- expression.
data Cont
  = MetaCont (ValueK -> S.Type -> CPS (TermK, S.Type))
  | ObjCont CoVar

-- Hmm. This is kind of the problem, isn't it?
-- by this point, the value has already been bound to a name, so now we have to
-- either have a trivial reassignment y := x, or perform a renaming
-- substitution (ugh), or something.
--
-- Maybe instead, have special cases for cps e (LetCont x t e' k), such as ???
-- This has something to do with cpsValue?
--
-- Alternatively, I could try to make it so that applyCont accepts a Value
-- rather than a TmVar, but that would probably take a major re-write.
-- applyCont (LetCont y t e2 k) x ty = _ -- assert t ~ ty

applyCont :: Cont -> ValueK -> S.Type -> CPS (TermK, S.Type)
applyCont (ObjCont k) v ty = pure (JumpK (CoVarK k) [v], ty)
applyCont (MetaCont f) v ty = f v ty

-- | A continuation can be /reified/ (turned into a 'CoValueK') by combining it
-- with the (source) type of the value it expects.
reifyCont :: Cont -> S.Type -> CPS (CoValueK, S.Type)
reifyCont (ObjCont k) ty = pure (CoVarK k, ty)
reifyCont (MetaCont f) ty =
  -- cont (x : ty) => f(x)
  freshTm "x" $ \x -> do
    ty' <- cpsType ty
    (e', t') <- f (VarValK x) ty
    let cont = ContDef [(x, ty')] e'
    pure (ContValK cont, t')

-- TODO: Consider fully-annotated variant of Source for easier CPS
-- every term is paired with its type. Somewhat redundant, but simplifies CPS
-- to take type as input rather than output. The elaboration pass that turns
-- Source into AnnSource also paves the way for future sugar and inference.

-- | Compute the Continuation-Passing Style transformation of a source term.
--
-- This requires the term to translate, as well as a continuation of type
-- 'Cont' that specifies what happens to the result of evaluating the
-- expression.
--
-- Returns an equivalent 'CPS.IR.TermK', as well as a source type that is
-- /probably/ the type of the expression, but I can't quite wrap my head around
-- it.
cps :: S.Term -> Cont -> CPS (TermK, S.Type)
cps (S.TmVarOcc x) k = do
  env <- asks cpsEnvCtx
  case Map.lookup x env of
    Nothing -> error "scope error"
    Just (x', t') -> applyCont k (VarValK x') t'
cps (S.TmCtorOcc c) k = do
  env <- asks cpsEnvCtors
  case Map.lookup c env of
    Nothing -> error "scope error"
    Just (c', t') -> applyCont k (VarValK c') t'
cps S.TmNil k = applyCont k NilValK S.TyUnit
cps (S.TmInt i) k = applyCont k (IntValK i) S.TyInt
cps (S.TmBool b) k = applyCont k (BoolValK b) S.TyBool
cps (S.TmString s) k = applyCont k (StringValK s) S.TyString
cps (S.TmChar c) k = applyCont k (CharValK c) S.TyChar
cps (S.TmLam x argTy e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (fun, ty) <- freshenVarBinds [(x, argTy)] $ \bs -> do
        (e', retTy) <- cps e (ObjCont k')
        s' <- cpsCoType retTy
        let fun = FunDef f (map (uncurry ValueParam) bs) [(k', s')] e'
        pure (fun, S.TyArr argTy retTy)
      (e'', t'') <- applyCont k (VarValK f) ty
      pure (LetFunK [fun] e'', t'')
cps (S.TmTLam aa ki e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' -> do
      (def, ty) <- freshenTyVarBinds [(aa, ki)] $ \bs -> do
        (e', retTy) <- cps e (ObjCont k')
        s' <- cpsCoType retTy
        let def = FunDef f (map (uncurry TypeParam) bs) [(k', s')] e'
        pure (def, S.TyAll aa ki retTy)
      (e'', t'') <- applyCont k (VarValK f) ty
      pure (LetFunK [def] e'', t'')
cps (S.TmFst e) k = 
  cps e $ MetaCont $ \z t -> do
    (ta, _tb) <- push t >>= \case
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- applyCont k (VarValK x) ta
      ta' <- cpsType ta
      let res = LetFstK x ta' z e'
      pure (res, t')
cps (S.TmSnd e) k = 
  cps e $ MetaCont $ \z t -> do
    (_ta, tb) <- push t >>= \case
      S.TyProd ta tb -> pure (ta, tb)
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- applyCont k (VarValK x) tb
      tb' <- cpsType tb
      let res = LetSndK x tb' z e'
      pure (res, t')
cps (S.TmFieldProj e f) k =
  cps e $ MetaCont $ \z t -> do
    tf <- push t >>= \case
      S.TyRecord fs -> case lookup f fs of
        Nothing -> error "type error"
        Just tf -> pure tf
      _ -> error "type error"
    freshTm "x" $ \x -> do
      (e', t') <- applyCont k (VarValK x) tf
      tf' <- cpsType tf
      let res = LetFieldK x tf' z (cpsFieldLabel f) e'
      pure (res, t')
cps (S.TmArith e1 op e2) k =
  cps e1 $ MetaCont $ \x _t1 -> do
    cps e2 $ MetaCont $ \y _t2 -> do
      freshTm "z" $ \z -> do
        (e', t') <- applyCont k (VarValK z) S.TyInt
        let res = LetArithK z (makeArith op x y) e'
        pure (res, t')
cps (S.TmNegate e) k =
  cps e $ MetaCont $ \x _t -> do
    freshTm "z" $ \z -> do
      (e', t') <- applyCont k (VarValK z) S.TyInt
      let res = LetArithK z (NegK x) e'
      pure (res, t')
cps (S.TmCmp e1 cmp e2) k =
  cps e1 $ MetaCont $ \x _t1 -> do
    cps e2 $ MetaCont $ \y _t2 -> do
      freshTm "z" $ \z -> do
        (e', t') <- applyCont k (VarValK z) S.TyBool
        let res = LetCompareK z (makeCompare cmp x y) e'
        pure (res, t')
cps (S.TmStringOp e1 op e2) k =
  cps e1 $ MetaCont $ \v1 _t1 -> do
    cps e2 $ MetaCont $ \v2 _t2 -> do
      freshTm "x" $ \x -> do
        let (op', ty) = makeStringOp op v1 v2
        (e', t') <- applyCont k (VarValK x) ty
        ty' <- cpsType ty
        let res = LetStringOpK x ty' op' e'
        pure (res, t')
cps (S.TmStringLength e) k =
  cps e $ MetaCont $ \x _t -> do
    freshTm "z" $ \z -> do
      (e', t') <- applyCont k (VarValK z) S.TyInt
      let res = LetStringOpK z IntK (LengthK x) e'
      pure (res, t')
cps (S.TmPair e1 e2) k =
  cps e1 $ MetaCont $ \v1 t1 ->
    cps e2 $ MetaCont $ \v2 t2 ->
      applyCont k (PairValK v1 v2) (S.TyProd t1 t2)
cps (S.TmRecord fields) k =
  cpsRecord fields [] k
cps (S.TmLet x t e1 e2) k = do
  -- [[let x:t = e1 in e2]] k
  -- -->
  -- let j = cont (x:t) => [[e2]] k; in [[e1]] j
  -- (This is similar to, but not quite the same as @case e1 of x:t -> e2@)
  -- (because a let-expression has no ctor to discriminate on)
  (cont, t2') <- cpsBranch [(x, t)] e2 k
  freshCo "j" $ \j -> do
    (e1', _t1') <- cps e1 (ObjCont j)
    pure (LetContK [(j, cont)] e1', t2')
cps (S.TmLetRec fs e) k =
  freshenRecBinds fs $ \fs' -> do
    fs'' <- traverse cpsFun fs'
    (e', t') <- cps e k
    let res = LetFunK fs'' e'
    pure (res, t')
cps (S.TmLetType al ad e) k =
  withAlias al ad $ cps e k
cps (S.TmApp e1 e2) k =
  cps e1 $ MetaCont $ \fv t1 -> do
    cps e2 $ MetaCont $ \xv _t2 -> do
      retTy <- push t1 >>= \case
        S.TyArr _argTy retTy -> pure retTy
        _ -> error "type error"
      (cont, t') <- reifyCont k retTy
      let res = CallK fv [ValueArg xv] [cont]
      pure (res, t')
cps (S.TmTApp e ty) k =
  cps e $ MetaCont $ \fv t1 -> do
    ty' <- cpsType ty
    instTy <- push t1 >>= \case
      S.TyAll aa _ki t1' -> pure (S.substType (S.singleSubst aa ty) t1')
      _ -> error "type error"
    (cont, t') <- reifyCont k instTy
    let res = CallK fv [TypeArg ty'] [cont]
    pure (res, t')
cps (S.TmPure e) k =
  -- let fun f (s : token#) (k2 : (token#, t) -> !) = k2 s z; in k f
  cps e $ MetaCont $ \z t ->
    freshTm "f_pure" $ \f -> do
      fun <- do
        freshTm "s" $ \s ->
          freshCo "k" $ \k' -> do
            let body = JumpK (CoVarK k') [VarValK s, z]
            t' <- cpsType t
            let fun = FunDef f [ValueParam s TokenK] [(k', ContK [TokenK, t'])] body
            pure fun
      (e', t') <- applyCont k (VarValK (funDefName fun)) (S.TyIO t)
      let res = LetFunK [fun] e'
      pure (res, t')
cps (S.TmBind x t e1 e2) k =
  cps e1 $ MetaCont $ \m1 _it1 ->
    freshTm "f_bind" $ \f -> do
      (fun, it2) <- do
        freshTm "s" $ \s1 ->
          freshCo "k" $ \k1 -> do
            (contDef, it2) <- freshTm "s" $ \s2 ->
              freshenVarBinds [(x, t)] $ \bs -> do
                -- I don't understand what I'm doing here. I hope it works.
                (e', it2) <- cps e2 $ MetaCont $ \m2 it2 -> do
                  let contBody = CallK m2 [ValueArg (VarValK s2)] [CoVarK k1]
                  pure (contBody, it2)
                pure (ContDef ((s2, TokenK) : bs) e', it2)
            t2' <- push it2 >>= \case
              S.TyIO t2 -> cpsType t2
              _ -> error "body of bind is not monadic"
            let funBody = CallK m1 [ValueArg (VarValK s1)] [ContValK contDef]
            let funDef = FunDef f [ValueParam s1 TokenK] [(k1, ContK [TokenK, t2'])] funBody
            pure (funDef, it2)
      -- dubious about the type here, but it seems to work.
      (e', t') <- applyCont k (VarValK (funDefName fun)) it2
      let res = LetFunK [fun] e'
      pure (res, t')
cps S.TmGetLine k = do
  -- let fun f (s : token#) (k2 : (token#, t) -> !) = let s2, msg <- getLine s in k2 s2 msg; k f
  freshTm "f_get" $ \f -> do
    fun <- do
      freshTm "s" $ \s1 ->
        freshCo "k" $ \k1 -> do
          freshTm "s" $ \s2 ->
            freshTm "x" $ \msg -> do
              let body = LetBindK s2 msg (PrimGetLine (VarValK s1)) (JumpK (CoVarK k1) [VarValK s2, VarValK msg])
              let fun = FunDef f [ValueParam s1 TokenK] [(k1, ContK [TokenK, StringK])] body
              pure fun
    (e', t') <- applyCont k (VarValK (funDefName fun)) (S.TyIO S.TyString)
    let res = LetFunK [fun] e'
    pure (res, t')
cps (S.TmPutLine e) k = do
  cps e $ MetaCont $ \z _t -> do
    freshTm "f_put" $ \f -> do
      fun <- do
        freshTm "s" $ \s1 ->
          freshCo "k" $ \k1 -> do
            freshTm "s" $ \s2 ->
              freshTm "u" $ \u -> do
                let body = LetBindK s2 u (PrimPutLine (VarValK s1) z) (JumpK (CoVarK k1) [VarValK s2, VarValK u])
                let fun = FunDef f [ValueParam s1 TokenK] [(k1, ContK [TokenK, UnitK])] body
                pure fun
      (e', t') <- applyCont k (VarValK (funDefName fun)) (S.TyIO S.TyUnit)
      let res = LetFunK [fun] e'
      pure (res, t')
cps (S.TmRunIO e) k = do
  cps e $ MetaCont $ \m it -> do
    retTy <- push it >>= \case
      S.TyIO t -> pure t
      _ -> error "cannot runIO non-monadic value"
    (cont, t') <- freshTm "s" $ \sv -> freshTm "x" $ \xv -> do
      retTy' <- cpsType retTy
      (e', t') <- applyCont k (VarValK xv) retTy
      pure (ContDef [(sv, TokenK), (xv, retTy')] e', t')
    freshTm "s" $ \s0 -> do
      let res = LetValK s0 TokenK TokenValK (CallK m [ValueArg (VarValK s0)] [ContValK cont])
      pure (res, t')
cps (S.TmIf e s et ef) k = do
  (coval, _) <- reifyCont k s
  nameJoinPoint coval $ \j addBinds -> do
    cps e $ MetaCont $ \z _t -> do
      (ef', _s') <- cps ef (ObjCont j)
      let contf = ContDef [] ef'
      (et', _s') <- cps et (ObjCont j)
      let contt = ContDef [] et'
      let res = IfK z contf contt
      pure (addBinds res, s)
cps (S.TmCase e s alts) k =
  cpsCase e k s alts

nameJoinPoint :: CoValueK -> (CoVar -> (TermK -> TermK) -> CPS (TermK, S.Type)) -> CPS (TermK, S.Type)
nameJoinPoint (CoVarK j) k = k j (\e -> e)
nameJoinPoint (ContValK cont) k = freshCo "j" $ \j -> k j (\e -> LetContK [(j, cont)] e)

cpsRecord :: [(S.FieldLabel, S.Term)] -> [(S.FieldLabel, S.Type, ValueK)] -> Cont -> CPS (TermK, S.Type)
cpsRecord [] ss k = do
  let fs = reverse ss
  let ty = S.TyRecord [(f, t) | (f, t, _) <- fs]
  let fields = [(cpsFieldLabel f, v) | (f, _, v) <- fs]
  applyCont k (RecordValK fields) ty
cpsRecord ((f, e) : fs) ss k =
  cps e $ MetaCont $ \v t ->
    cpsRecord fs ((f, t, v) : ss) k

cpsFieldLabel :: S.FieldLabel -> FieldLabel
cpsFieldLabel (S.FieldLabel f) = FieldLabel f

-- Note: CPS translation of let-expressions:
--
-- This translation is actually slightly suboptimal, as mentioned by
-- [Compiling with Continuations, Continued].
-- Consider the translation of 'let x : int = 17 in x'. The current
-- translation will yield
--  let cont j (x : int) =
--    halt x
--  in
--  let t0 : int = 17 in
--  j t0
-- A more efficient translation would be simply
--  let x : int = 17 in
--  halt x
-- To implement this, I would have to examine the expression 'e1' to see if
-- it is a value (or function value), and pass that to the continuation
-- directly instead of reify/jump.
--
-- ==> LetCont along with ObjCont and MetaCont? 'LetCont x t e c' means
-- "after this, bind result value to x:t and pass result to CPS[e] c"??

-- | An auxiliary type for named function definitions, produced while
-- performing CPS translation of letrec-expressions.
data TmFun
  -- | @f (x : t) : t' = e@
  = TmFun S.TmVar S.TmVar S.Type S.Type S.Term
  -- | @f \@a : t' = e@
  | TmTFun S.TmVar S.TyVar S.Kind S.Type S.Term

-- | Translate a function definition into continuation-passing style.
cpsFun :: TmFun -> CPS FunDef
cpsFun (TmFun f x t s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable)"
      Just (f', _) -> pure f'
    fun <- freshenVarBinds [(x, t)] $ \bs -> do
      (e', _s') <- cps e (ObjCont k)
      s' <- cpsCoType s
      pure (FunDef f' (map (uncurry ValueParam) bs) [(k, s')] e')
    pure fun
cpsFun (TmTFun f aa ki s e) =
  freshCo "k" $ \k -> do
    env <- asks cpsEnvCtx
    -- Recursive bindings already handled, outside of this.
    f' <- case Map.lookup f env of
      Nothing -> error "cpsFun: function not in scope (unreachable)"
      Just (f', _) -> pure f'
    fun <- freshenTyVarBinds [(aa, ki)] $ \bs -> do
      (e', _s') <- cps e (ObjCont k)
      s' <- cpsCoType s
      pure (FunDef f' (map (uncurry TypeParam) bs) [(k, s')] e')
    pure fun

-- | CPS-transform a case expression.
cpsCase :: S.Term -> Cont -> S.Type -> [(S.Ctor, [(S.TmVar, S.Type)], S.Term)] -> CPS (TermK, S.Type)
cpsCase e k s alts = do
  (coval, _) <- reifyCont k s
  nameJoinPoint coval $ \j addBindsTo -> do
    (e', t') <- cpsCase' e j s alts
    pure (addBindsTo e', t')

-- | CPS-transform a case analysis, given a scrutinee, a continuation variable,
-- a return type, and a list of branches with bound variables.
cpsCase' :: S.Term -> CoVar -> S.Type -> [(S.Ctor, [(S.TmVar, S.Type)], S.Term)] -> CPS (TermK, S.Type)
cpsCase' e j s alts =
  cps e $ MetaCont $ \z t -> do
    res <- cpsBranches z t j alts
    pure (res, s)

cpsBranches :: ValueK -> S.Type -> CoVar -> [(S.Ctor, [(S.TmVar, S.Type)], S.Term)] -> CPS TermK
cpsBranches z t j bs = do
  tcapp <- cpsType t >>= \t' -> case asTyConApp t' of
    Nothing -> error "cannot perform case analysis on this type"
    Just app -> pure app
  -- CPS each branch
  conts <- for bs $ \ (S.Ctor c, xs, e) -> do
    (cont, _s') <- cpsBranch xs e (ObjCont j)
    pure (Ctor c, ContValK cont)
  pure (CaseK z tcapp conts)

-- | CPS-transform a case alternative @(x:t)+ -> e@.
--
-- @cpsBranch xs e k@ returns @(cont xs = [[e]] k;, s)@ where @s@ is the
-- type of @e@.
cpsBranch :: [(S.TmVar, S.Type)] -> S.Term -> Cont -> CPS (ContDef, S.Type)
cpsBranch xs e k = freshenVarBinds xs $ \xs' -> do
  (e', s') <- cps e k
  pure (ContDef xs' e', s')


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

makeCtorWrapper :: TyCon -> Ctor -> [(TyVar, KindK)] -> [TypeK] -> TermK -> CPS TermK
makeCtorWrapper tc c ctorparams ctorargs e = do
  (w, _) <- go (let Ctor tmp = c in TmVar tmp 0) (ctorparams, ctorargs) ([], []) e
  pure w
  where
    go :: TmVar -> ([(TyVar, KindK)], [TypeK]) -> ([TypeK], [TmVar]) -> TermK -> CPS (TermK, TypeK)
    go name ([], []) (tyarglist, tmarglist) body = do
      let val = CtorValK c tyarglist (map VarValK tmarglist)
      let wrapperTy = fromTyConApp (TyConApp tc [TyVarOccK aa | (aa, _) <- ctorparams])
      -- let wrapperTy = foldl (\t (aa, _) -> TyAppK t (TyVarOccK aa)) (TyConOccK tc) ctorparams
      let wrapper = LetValK name wrapperTy val body
      pure (wrapper, wrapperTy)
    go name ((aa, k) : tyargs, tmargs) (tyarglist, tmarglist) body = do
      freshTm "w" $ \newName ->
        freshCo "k" $ \newCont -> do
          (inner, innerTy) <- go newName (tyargs, tmargs) (tyarglist ++ [TyVarOccK aa], tmarglist) (JumpK (CoVarK newCont) [VarValK newName])
          let fun = FunDef name [TypeParam aa k] [(newCont, ContK [innerTy])] inner
          let wrapper = LetFunK [fun] body
          pure (wrapper, FunK [TypeTele aa k] [ContK [innerTy]])
    go name ([], argTy : tmargs) (tyarglist, tmarglist) body = do
      freshTm "w" $ \newName ->
        freshTm "arg" $ \newArg ->
          freshCo "k" $ \newCont -> do
            (inner, innerTy) <- go newName ([], tmargs) (tyarglist, tmarglist ++ [newArg]) (JumpK (CoVarK newCont) [VarValK newName])
            let fun = FunDef name [ValueParam newArg argTy] [(newCont, ContK [innerTy])] inner
            let wrapper = LetFunK [fun] body
            pure (wrapper, FunK [ValueTele argTy] [ContK [innerTy]])

makeDataWrapper :: DataDecl -> TermK -> CPS TermK
makeDataWrapper (DataDecl tc _ ctors) e = go ctors e
  where
    go [] e' = pure e'
    go (CtorDecl c params args : cs) e' = makeCtorWrapper tc c params args =<< go cs e'

addCtorWrappers :: [DataDecl] -> TermK -> CPS TermK
addCtorWrappers [] e = pure e
addCtorWrappers (dd : ds) e = makeDataWrapper dd =<< addCtorWrappers ds e

cpsDataDecl :: S.DataDecl -> CPS DataDecl
cpsDataDecl (S.DataDecl (S.TyCon tc) params ctors) = do
  kind <- cpsKind $ foldr (\ (_aa, k1) k2 -> S.KiArr k1 k2) S.KiStar params
  freshenTyVarBinds params $ \params' -> do
    ctors' <- traverse (cpsCtorDecl params') ctors
    pure (DataDecl (TyCon tc) kind ctors')

cpsCtorDecl :: [(TyVar, KindK)] -> S.CtorDecl -> CPS CtorDecl
cpsCtorDecl params' (S.CtorDecl (S.Ctor c) args) = CtorDecl (Ctor c) params' <$> traverse cpsType args

ctorWrapperBinds :: S.DataDecl -> [(S.Ctor, (TmVar, S.Type))]
ctorWrapperBinds (S.DataDecl tc params ctors) = map ctorDeclType ctors
  where
    ctorDeclType :: S.CtorDecl -> (S.Ctor, (TmVar, S.Type))
    ctorDeclType (S.CtorDecl (S.Ctor c) args) = (S.Ctor c, (TmVar c 0, ty))
      where
        ret = foldl S.TyApp (S.TyConOcc tc) (map (S.TyVarOcc . fst) params)
        ty = foldr (uncurry S.TyAll) (foldr S.TyArr ret args) params


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
  , cpsEnvAliases :: Map S.Alias S.AliasDef
  }

emptyEnv :: CPSEnv
emptyEnv = CPSEnv Map.empty Map.empty Map.empty Map.empty Map.empty

withAlias :: S.Alias -> S.AliasDef -> CPS a -> CPS a
withAlias al ad m = do
  let extend env = env { cpsEnvAliases = Map.insert al ad (cpsEnvAliases env) }
  local extend m

-- Hmm. I'm starting to think that maybe I should only be using
-- 'freshenVarBinds' instead of freshTm directly. (I.E., for reasons of having
-- things be in the correct typing context)
freshTm :: String -> (TmVar -> CPS a) -> CPS a
freshTm x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = TmVar x i
  let extend env = env { cpsEnvScope = Map.insert x (i+1) (cpsEnvScope env) }
  local extend (k x')

freshCo :: String -> (CoVar -> CPS a) -> CPS a
freshCo x k = do
  scope <- asks cpsEnvScope
  let i = fromMaybe 0 (Map.lookup x scope)
  let x' = CoVar x i
  let extend env = env { cpsEnvScope = Map.insert x (i+1) (cpsEnvScope env) }
  local extend (k x')

insertMany :: Ord k => Foldable t => t (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

-- | Rename a sequence of variable bindings and bring them in to scope.
freshenVarBinds :: Traversable t => t (S.TmVar, S.Type) -> (t (TmVar, TypeK) -> CPS a) -> CPS a
freshenVarBinds bs k = do
  scope <- asks cpsEnvScope
  let
    pick sc (S.TmVar x, t) =
      let i = fromMaybe 0 (Map.lookup x sc) in
      let x' = TmVar x i in
      (Map.insert x (i+1) sc, (S.TmVar x, (x', t)))
    (sc', bs') = mapAccumL pick scope bs
  let extend env = env { cpsEnvScope = sc', cpsEnvCtx = insertMany bs' (cpsEnvCtx env) }
  bs'' <- traverse (\ (_, (x', t)) -> (,) x' <$> cpsType t) bs'
  local extend (k bs'')

freshenTyVarBinds :: Traversable t => t (S.TyVar, S.Kind) -> (t (TyVar, KindK) -> CPS a) -> CPS a
freshenTyVarBinds bs k = do
  scope <- asks cpsEnvScope
  let
    -- pick :: Map String Int -> (S.TyVar, S.Kind) -> (Map String Int, (S.TyVar, TyVar))
    pick sc (S.TyVar aa, ki) =
      let i = fromMaybe 0 (Map.lookup aa scope) in
      let aa' = TyVar aa i in
      (Map.insert aa (i+1) sc, (S.TyVar aa, (aa', ki)))
    (sc', bs') = mapAccumL pick scope bs
  let extend env = env { cpsEnvScope = sc', cpsEnvTyCtx = insertMany bs' (cpsEnvTyCtx env) }
  bs'' <- traverse (\ (_, (aa', ki)) -> (,) aa' <$> cpsKind ki) bs'
  local extend (k bs'')

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
  let extend env = env { cpsEnvScope = sc', cpsEnvCtx = insertMany binds (cpsEnvCtx env) }
  fs' <- for fs $ \ (f, ty, rhs) -> do
    push ty >>= \ty' -> case (ty', rhs) of
      (S.TyArr _t s, S.TmLam x t' body) -> do
        pure (TmFun f x t' s body)
      (S.TyAll aa _k1 t, S.TmTLam bb k2 body) -> do
        let sub = S.singleSubst aa (S.TyVarOcc bb)
        pure (TmTFun f bb k2 (S.substType sub t) body)
      (_, _) -> error "letrec error"
  local extend (k fs')


