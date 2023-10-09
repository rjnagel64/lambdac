{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving, DerivingStrategies #-}
-- {-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Experiments.CPS3 where


import Data.Traversable (for)
import Control.Monad.State
import Control.Monad.Reader

import qualified Data.Map as Map
import Data.Map (Map)

-- A modified form of CPS that does not perform full ANF-style flattening.
-- Instead, applyCont :: Cont -> Value -> M Term

data Var = Var String | Gen Int
  deriving (Eq, Ord)

newtype CoVar = CoVar Int
  deriving (Eq, Ord)

newtype Ctor = Ctor String

data Src'
  = SVar Var
  | SApp Src Src
  | SLam Var Src
  | SInt Int
  | SBinOp Src BinOp Src
  | SLet Var Src Src
  | SPair Src Src
  | SFst Src
  | SSnd Src
  | SInl Src
  | SInr Src
  | SCase Src (Var, Src) (Var, Src)
  -- let rec f : t = \x -> e1 in e2
  | SLetRec Var STy Var Src Src

data Src = Src Src' STy

data BinOp = Add | Subtract | Multiply

typeof :: Src -> STy
typeof (Src _ t) = t

data STy = SArrTy STy STy | SIntTy | SPairTy STy STy | SSumTy STy STy

data Core
  = CLetVal Var Ty Value Core
  | CLetCoVal CoVar CoTy CoValue Core
  -- Hmm. Should the callable be a variable or a value? Yep, value.
  -- Redexes in the source program linger as redexes in the CPS'ed program.
  | CCall Value Value CoValue
  | CJump CoValue Value
  | CCase Value [(Ctor, CoValue)]
  | CLetFst Var Ty Value Core
  | CLetSnd Var Ty Value Core
  | CLetBinOp Var Ty BinOp Value Value Core
  -- let rec f (x : t) (k : s) = e1 in e2
  | CLetRec Var (Var, Ty) (CoVar, CoTy) Core Core

data Value
  = VVar Var
  | VInt Int
  | VPair Value Value
  | VInl Ty Ty Value
  | VInr Ty Ty Value
  | VFun (Var, Ty) (CoVar, CoTy) Core

data CoValue
  = CVVar CoVar
  | CVCont Cont

data Cont = Cont (Var, Ty) Core

data Ty = FunTy Ty CoTy | IntTy | PairTy Ty Ty | SumTy Ty Ty
data CoTy = ContTy Ty

contTy :: Cont -> CoTy
contTy (Cont (x, t) e) = ContTy t



newtype M a = M { getM :: State Int a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadState Int M

data Kont
  = ObjKont CoVar
  | MetaKont STy (Value -> M Ans)
  | LetKont Var STy Src Kont

data Ans = Ans Core

applyCont :: Kont -> Value -> M Ans
applyCont (ObjKont k) v = do
  pure (Ans (CJump (CVVar k) v))
applyCont (MetaKont t f) v = f v
applyCont (LetKont x t e kont) v = do
  Ans e' <- cps e kont
  pure (Ans (CLetVal x (cpsTy t) v e'))

reifyCont :: Kont -> M CoValue
reifyCont (ObjKont k) = pure (CVVar k)
reifyCont (MetaKont t f) = do
  freshTm $ \x -> do
    Ans e' <- f (VVar x)
    pure (CVCont (Cont (x, cpsTy t) e'))
reifyCont (LetKont x t e kont) = do
  Ans e' <- cps e kont
  pure (CVCont (Cont (x, cpsTy t) e'))

-- Hmm. newtype FreshT = StateT Int
-- class MonadFresh m where
--   freshTm :: (Var -> m a) -> m a
--   freshCo :: (CoVar -> m a) -> m a
-- instance MonadTrans FreshT
-- instance MonadFresh m => MonadFresh (ReaderT r m) where
--   freshTm kont = lift (freshTm (lift . kont)) -- ???
--   freshCo kont = lift (freshCo (lift . kont)) -- ???
freshCo :: MonadState Int m => (CoVar -> m a) -> m a
freshCo cont = do
  i <- get
  modify' (+1)
  cont (CoVar i)

freshTm :: MonadState Int m => (Var -> m a) -> m a
freshTm cont = do
  i <- get
  modify' (+1)
  cont (Gen i)


cpsTy :: STy -> Ty
cpsTy (SArrTy t1 t2) = FunTy (cpsTy t1) (cpsCoTy t2)
cpsTy SIntTy = IntTy
cpsTy (SPairTy t1 t2) = PairTy (cpsTy t1) (cpsTy t2)
cpsTy (SSumTy t1 t2) = SumTy (cpsTy t1) (cpsTy t2)

cpsCoTy :: STy -> CoTy
cpsCoTy t = ContTy (cpsTy t)

cps :: Src -> Kont -> M Ans
cps (Src (SVar x) t) kont = applyCont kont (VVar x)
cps (Src (SApp e1 e2) t) kont =
  cps e1 $ MetaKont (typeof e1) $ \fnVal ->
    cps e2 $ MetaKont (typeof e2) $ \argVal -> do
      coVal <- reifyCont kont
      pure (Ans (CCall fnVal argVal coVal))
cps (Src (SLam x e) (SArrTy t1 t2)) kont =
  freshCo $ \k -> do
    Ans e' <- cps e (ObjKont k)
    let v = VFun (x, cpsTy t1) (k, cpsCoTy t2) e'
    applyCont kont v
cps (Src (SLam _ _) _) _ = error "SLam cannot have this type."
cps (Src (SInt i) SIntTy) kont = applyCont kont (VInt i)
cps (Src (SInt _) _) _ = error "SInt cannot have this type."
cps (Src (SBinOp e1 op e2) t) kont =
  cps e1 $ MetaKont (typeof e1) $ \v1 ->
    cps e2 $ MetaKont (typeof e2) $ \v2 ->
      freshTm $ \x -> do
        Ans e' <- applyCont kont (VVar x)
        pure (Ans (CLetBinOp x (cpsTy t) op v1 v2 e'))
-- This is the inefficient let-rule
-- let x = 17 in e
-- becomes
-- let j (x : int) = e
-- in
-- j 17
-- when it should be
-- let x : int = 17 in e
-- ... actually, why do I not emit any CLetVal statements?
-- if isValue(e1) then CLetVal x (typeof e1) (asValue e1) (cps e2 kont)
-- else freshCo j; let j = cont (x : typeof e1) => cps e2 kont in cps e1 j
-- cps (Src (SLet x e1 e2) t) kont = do
--   coVal <- cpsBranch (x, typeof e1) e2 kont
--   freshCo $ \j -> do
--     Ans e1' <- cps e1 $ ObjKont j
--     let e' = CLetCoVal j (cpsCoTy (typeof e1)) coVal e1'
--     pure (Ans e')
cps (Src (SLet x e1 e2) t) kont = cps e1 (LetKont x (typeof e1) e2 kont)
-- Hmm. I think LetKont may in fact be redundant with MetaKont:
-- cps (Src (SLet x e1 e2) t) kont =
--   cps e1 $ MetaKont (typeof e1) $ \v -> do
--     Ans e2' <- cps e2 kont
--     pure (Ans (CLetVal x (cpsTy (typeof e1)) v e'))
-- TODO: cps LetRec
cps (Src (SLetRec f (SArrTy t1 t2) x e1 e2) t') kont = do
  -- Should be pretty similar to SLam.
  (k, e1') <- freshCo $ \k -> do
    Ans e1' <- cps e1 $ ObjKont k
    pure (k, e1')
  Ans e2' <- cps e2 kont
  pure (Ans (CLetRec f (x, cpsTy t1) (k, cpsCoTy t2) e1' e2'))
cps (Src (SLetRec _ _ _ _ _) _) _ = error "a letrec-bound function cannot have this type."
cps (Src (SPair e1 e2) t) kont =
  cps e1 $ MetaKont (typeof e1) $ \v1 ->
    cps e2 $ MetaKont (typeof e2) $ \v2 -> do
      let v = VPair v1 v2
      applyCont kont v
cps (Src (SInl e) (SSumTy t1 t2)) kont =
  cps e $ MetaKont (typeof e) $ \v ->
    applyCont kont (VInl (cpsTy t1) (cpsTy t2) v)
cps (Src (SInl _) _) _ = error "inl cannot have this type."
cps (Src (SInr e) (SSumTy t1 t2)) kont =
  cps e $ MetaKont (typeof e) $ \v ->
    applyCont kont (VInr (cpsTy t1) (cpsTy t2) v)
cps (Src (SInr _) _) _ = error "inr cannot have this type."
cps (Src (SFst e) t) kont =
  cps e $ MetaKont (typeof e) $ \v ->
    freshTm $ \x -> do
      Ans e' <- applyCont kont (VVar x)
      pure (Ans (CLetFst x (cpsTy t) v e'))
cps (Src (SSnd e) t) kont =
  cps e $ MetaKont (typeof e) $ \v ->
    freshTm $ \x -> do
      Ans e' <- applyCont kont (VVar x)
      pure (Ans (CLetSnd x (cpsTy t) v e'))
cps (Src (SCase e (x, e1) (y, e2)) t) kont =
  case typeof e of
    SSumTy t1 t2 ->
      cpsCase e kont [(Ctor "inl", (x, t1), e1), (Ctor "inr", (y, t2), e2)]
    _ -> error "scrutinee of SCase cannot have this type."

type SrcAlt = (Ctor, (Var, STy), Src)

cpsCase :: Src -> Kont -> [SrcAlt] -> M Ans
cpsCase e kont alts = do
  coval <- reifyCont kont
  nameJoinPoint coval (typeof e) $ \j addBindsTo -> do
    Ans e' <- cpsCase' e j alts
    pure (Ans (addBindsTo e'))

cpsCase' :: Src -> CoVar -> [SrcAlt] -> M Ans
cpsCase' e j alts = do
  cps e $ MetaKont (typeof e) $ \v -> do
    cpsBranches v j alts

cpsBranches :: Value -> CoVar -> [SrcAlt] -> M Ans
cpsBranches v j alts = do
  alts' <- for alts $ \ (c, (x, t), e) -> do
    cont <- cpsBranch (x, t) e (ObjKont j)
    pure (c, cont)
  pure (Ans (CCase v alts'))

-- Hmm. If I add HaltKont, this may introduce a trivial binding.
-- I suppose instead I could pass an 'AtomicKont = CoVar | Halt' to the
-- continuation instead.
nameJoinPoint :: CoValue -> STy -> (CoVar -> (Core -> Core) -> M a) -> M a
nameJoinPoint (CVVar k) _t kont = kont k (\e' -> e')
nameJoinPoint (CVCont cont) t kont =
  freshCo $ \j -> do
    kont j (\e' -> CLetCoVal j (cpsCoTy t) (CVCont cont) e')

cpsBranch :: (Var, STy) -> Src -> Kont -> M CoValue
cpsBranch (x, t) e kont = do
  Ans e' <- cps e kont
  pure (CVCont (Cont (x, cpsTy t) e'))




data ANF
  = AHalt Var
  | ACall Var Var CoVar
  | AJump CoVar Var
  | ACase Var [(Ctor, CoVar)]
  | ALetVal Var Ty ANFValue ANF
  | ALetCoVal CoVar CoTy ANFCoValue ANF
  | ALetFst Var Ty Var ANF
  | ALetSnd Var Ty Var ANF
  | ALetBinOp Var Ty BinOp Var Var ANF
  | ALetRec Var (Var, Ty) (CoVar, CoTy) ANF ANF

data ANFValue
  = AVPair Var Var
  | AVInt Int
  | AVInl Ty Ty Var
  | AVInr Ty Ty Var

data ANFCoValue
  = ACVCont ANFCont

data ANFCont = ACont (Var, Ty) ANF

-- map var (var, ty) to deal with renaming
-- will need to actually bring variables into scope if I do this.
newtype N a = N { getN :: StateT Int (Reader Env) a }
data Env = Env { envTms :: Map Var (Var, Ty), envCos :: Map CoVar (CoVar, CoTy) }

deriving newtype instance Functor N
deriving newtype instance Applicative N
deriving newtype instance Monad N
deriving newtype instance MonadReader Env N
deriving newtype instance MonadState Int N

toANF :: Core -> N ANF
toANF (CJump coval argval) =
  nameCo coval $ \kvar kty addCoBind ->
    nameTm argval $ \avar aty addArgBind ->
      pure (addCoBind (addArgBind (AJump kvar avar)))
toANF (CCall fnval argval coval) =
  nameTm fnval $ \fvar fty addFnBind ->
    nameTm argval $ \avar aty addArgBind ->
      nameCo coval $ \kvar kty addCoBind ->
        pure $ addFnBind (addArgBind (addCoBind (ACall fvar avar kvar)))
toANF (CCase v alts) =
  nameTm v $ \x _t addX ->
    nameAlts alts $ \alts' addAlts ->
      pure $ addX (addAlts (ACase x alts'))
toANF (CLetVal x t v e) =
  -- To convert
  --   let x = v in e
  -- to ANF, we first give y a name:
  --   let y = v; let x = y in e
  -- However, let x = y is forbidden in ANF, so we have to introduce a
  -- renaming, finally yielding
  --   let y = v in e[x := y]
  nameTm v $ \y _t' addY ->
    renameVar x y t $ do
      e' <- toANF e
      pure (addY e')
toANF (CLetCoVal k s v e) =
  nameCo v $ \j _s' addJ ->
    renameCoVar k j s $ do
      e' <- toANF e
      pure (addJ e')
toANF (CLetRec f (x, t) (k, s) e1 e2) = do
  e1' <- toANF e1
  e2' <- toANF e2
  pure (ALetRec f (x, t) (k, s) e1' e2')
toANF (CLetFst x t v e) =
  nameTm v $ \y _t' addY -> do
    e' <- toANF e
    pure (addY (ALetFst x t y e'))
toANF (CLetSnd x t v e) =
  nameTm v $ \y _t' addY -> do
    e' <- toANF e
    pure (addY (ALetSnd x t y e'))
toANF (CLetBinOp x t op v1 v2 e) =
  nameTm v1 $ \y1 t1 add1 ->
    nameTm v2 $ \y2 t2 add2 -> do
      e' <- toANF e
      pure (add1 (add2 (ALetBinOp x t op y1 y2 e')))

renameVar :: Var -> Var -> Ty -> N a -> N a
renameVar x y t m = local extend m
  where extend env = env { envTms = Map.insert x (y, t) (envTms env) }

renameCoVar :: CoVar -> CoVar -> CoTy -> N a -> N a
renameCoVar k j s m = local extend m
  where extend env = env { envCos = Map.insert k (j, s) (envCos env) }

nameAlts :: [(Ctor, CoValue)] -> ([(Ctor, CoVar)] -> (ANF -> ANF) -> N a) -> N a
nameAlts [] kont = kont [] (\e' -> e')
nameAlts ((c, coval) : alts) kont =
  nameCo coval $ \k ty addK ->
    nameAlts alts $ \alts' addAlts ->
      kont ((c, k) : alts') (addK . addAlts)

nameTm :: Value -> (Var -> Ty -> (ANF -> ANF) -> N a) -> N a
nameTm (VVar x) kont = do
  env <- asks envTms
  let (x', ty) = env Map.! x
  kont x' ty (\e' -> e')
nameTm (VInt i) kont =
  freshTm $ \x ->
    let ty = IntTy in
    kont x ty (\e' -> ALetVal x ty (AVInt i) e')
nameTm (VPair v1 v2) kont =
  nameTm v1 $ \x1 t1 add1 ->
    nameTm v2 $ \x2 t2 add2 ->
      freshTm $ \x ->
        let ty = PairTy t1 t2 in
        kont x ty (\e' -> add1 (add2 (ALetVal x ty (AVPair x1 x2) e')))
nameTm (VInl t1 t2 v) kont =
  nameTm v $ \x t addX ->
    freshTm $ \y ->
      let ty = SumTy t1 t2 in
      kont y ty (\e' -> ALetVal y ty (AVInl t1 t2 x) e')
nameTm (VInr t1 t2 v) kont =
  nameTm v $ \x t addX ->
    freshTm $ \y ->
      let ty = SumTy t1 t2 in
      kont y ty (\e' -> ALetVal y ty (AVInr t1 t2 x) e')
nameTm (VFun (x, t) (k, s) body) kont =
  freshTm $ \f -> do
    body' <- toANF body
    let ty = FunTy t s
    kont f ty (\e' -> ALetRec f (x, t) (k, s) body' e')

nameCo :: CoValue -> (CoVar -> CoTy -> (ANF -> ANF) -> N a) -> N a
nameCo (CVVar k) kont = do
  env <- asks envCos
  let (k', ty) = env Map.! k
  kont k' ty (\e' -> e')
nameCo (CVCont cont@(Cont (x, t) e)) kont = do
  cont' <- do
    -- cont' <- withTm (x, t) $ ACont (x, t) <$> toANF e
    e' <- toANF e
    pure (ACont (x, t) e')
  freshCo $ \k ->
    let ty = contTy cont in
    kont k ty (\e' -> ALetCoVal k ty (ACVCont cont') e')

main :: IO ()
main = putStrLn "Hello, World!"
