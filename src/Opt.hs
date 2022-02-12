{-# LANGUAGE StandaloneDeriving, DerivingVia, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Opt where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Int
import Data.Traversable (for)

import Control.Monad.Reader
import Control.Monad.Writer

-- [Compiling with Continuations, Continued] mostly.
-- CPS transformation, Closure Conversion, hopefully C code generation.

-- TODO: Reread "Compiling with Continuations and LLVM" for ideas about C code
-- generation

-- | Term variables stand for values
newtype TmVar = TmVar String
  deriving (Eq, Ord)

-- | Continuation variables name basic blocks and jump targets.
newtype CoVar = CoVar String
  deriving (Eq, Ord)

-- | Function names reference functions or closures.
newtype FnName = FnName String

-- TODO: Add booleans and if-expressions. They can be compiled more efficiently
-- than case analysis on Either () ().
data Term
  -- x
  = TmVarOcc TmVar
  -- case e of inl x -> e1; inr y -> e2
  | TmCase Term TmVar Term TmVar Term
  -- inl e
  | TmInl Term
  -- inr e
  | TmInr Term
  -- \x.e
  | TmLam TmVar Term
  -- e1 e2
  | TmApp Term Term
  -- (e1, e2)
  | TmPair Term Term
  -- fst e
  | TmFst Term
  -- snd e
  | TmSnd Term
  -- let x = e1 in e2
  | TmLet TmVar Term Term
  -- let rec fs+ in e
  | TmRecFun [TmFun] Term
  -- ()
  | TmNil

-- TODO: More primops.
-- let y = primop(x+) in e
-- LetPrimK :: TmVar -> PrimOp -> TermK -> TermK
-- data PrimOp = PrimAddInt32 TmVar TmVar
--
-- Are there primops that take CoVar:s? Probably.

-- TODO: Add booleans and an if-expression.

-- f x := e
data TmFun = TmFun TmVar TmVar Term

data Type
  = TySum Type Type
  | TyProd Type Type
  | TyArr Type Type
  | TyUnit

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
  -- let rec ks in e
  | LetContK [ContDef] TermK
  -- let rec fs in e
  | LetFunK [FunDef] TermK

  -- Block terminators
  -- k x, goto k(x)
  | JumpK CoVar TmVar
  -- f x k, call f(x, k)
  | CallK TmVar TmVar CoVar
  -- case x of k1 | k2, branch
  | CaseK TmVar CoVar CoVar

-- | Named basic blocks
-- k x := e
data ContDef = ContDef CoVar TmVar TermK

-- | Function definitions
-- f x k := e
data FunDef = FunDef TmVar TmVar CoVar TermK

-- | Values require no evaluation.
-- This can be compiled as struct containing pointers
data ValueK
  = NilK
  | PairK TmVar TmVar
  | InlK TmVar
  | InrK TmVar

data TypeK
  -- unit
  = UnitK
  -- σ × τ
  | ProdK TypeK TypeK
  -- σ + τ
  | SumK TypeK TypeK
  -- σ -> τ
  -- Application requires argument variable of type σ, continuation variable of
  -- type τ.
  | ArrK TypeK TypeK


-- | CPS-convert a term.
--
-- TODO: Complete these
-- TODO: Find a way to reduce the nesting.
-- ContT r m a = (a -> m r) -> m r
-- Term -> ContT TermK FreshM TmVar
-- The real question is, does it behave properly.
cps :: Term -> (TmVar -> FreshM TermK) -> FreshM TermK
cps (TmVarOcc x) k = k x
cps (TmLam x e) k =
  freshTm "f" $ \f ->
    freshCo "k" $ \k' ->
      let mkFun e' = [FunDef f x k' e'] in
      LetFunK <$> (mkFun <$> cpsTail e k') <*> k f
cps (TmRecFun fs e) k = do
  LetFunK <$> traverse cpsFun fs <*> cps e k
cps (TmApp e1 e2) k =
  cps e1 $ \v1 ->
    cps e2 $ \v2 ->
      freshCo "k" $ \kv ->
        freshTm "x" $ \xv -> do
          e <- k xv
          pure $ LetContK [ContDef kv xv e] (CallK v1 v2 kv)
cps (TmInl e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      LetValK x (InlK z) <$> k x
cps (TmInr e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      LetValK x (InrK z) <$> k x
cps (TmCase e xl el xr er) k =
  cps e $ \z ->
    freshCo "j" $ \j ->
      freshTm "x" $ \x ->
        freshCo "k1" $ \k1 ->
          freshCo "k2" $ \k2 -> do
            el' <- cpsTail el j
            er' <- cpsTail er j
            e' <- k x
            pure $
              LetContK [ContDef j x e'] $
                LetContK [ContDef k1 xl el'] $
                  LetContK [ContDef k2 xr er'] $
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
cps TmNil k =
  freshTm "x" $ \x -> LetValK x NilK <$> k x
cps (TmLet x e1 e2) k = do
  e2' <- cps e2 k
  freshCo "j" $ \j ->
    LetContK [ContDef j x e2'] <$> cpsTail e1 j

cpsFun :: TmFun -> FreshM FunDef
cpsFun (TmFun f x e) = freshCo "k" $ \k -> FunDef f x k <$> cpsTail e k

-- | CPS-convert a term in tail position.
-- In tail position, the continuation is always a continuation variable, which
-- allows for simpler translations.
cpsTail :: Term -> CoVar -> FreshM TermK
cpsTail (TmVarOcc x) k = pure (JumpK k x)
cpsTail (TmInl e) k =
  cps e $ \z ->
    freshTm "x" $ \x ->
      pure (LetValK x (InlK z) (JumpK k x))
cpsTail (TmPair e1 e2) k =
  cps e1 $ \x1 ->
    cps e2 $ \x2 ->
      freshTm "x" $ \x ->
        pure (LetValK x (PairK x1 x2) (JumpK k x))


newtype FreshM a = FreshM { runFreshM :: Reader (Map String Int) a }

deriving via Reader (Map String Int) instance Functor FreshM
deriving via Reader (Map String Int) instance Applicative FreshM
deriving via Reader (Map String Int) instance Monad FreshM
deriving via Reader (Map String Int) instance MonadReader (Map String Int) FreshM

freshTm :: String -> (TmVar -> FreshM a) -> FreshM a
freshTm x k = do
  scope <- ask
  case Map.lookup x scope of
    Nothing -> local (Map.insert x 0) (k (TmVar (x ++ "0")))
    Just i -> local (Map.insert x (i+1)) (k (TmVar (x ++ show i)))

freshCo :: String -> (CoVar -> FreshM a) -> FreshM a
freshCo x k = do
  scope <- ask
  case Map.lookup x scope of
    Nothing -> local (Map.insert x 0) (k (CoVar (x ++ "0")))
    Just i -> local (Map.insert x (i+1)) (k (CoVar (x ++ show i)))

runFresh :: FreshM a -> a
runFresh = flip runReader Map.empty . runFreshM


-- TODO: Figure out call-pattern specialization
-- contify is basically call-pattern specialization for continuation arguments?
-- TODO: Implement Call Arity to be smarter about passing multiple arguments
-- together.

newtype InlineM a = InlineM { runInlineM :: Reader InlineEnv a }

-- GND is less verbose, at least.
deriving newtype instance Functor InlineM
deriving newtype instance Applicative InlineM
deriving newtype instance Monad InlineM
deriving newtype instance MonadReader InlineEnv InlineM

data InlineEnv
  = InlineEnv {
  -- | Functions and continuations larger than the threshold will not be
  -- inlined.
  -- TODO: different threshold for fun/cont?
    inlineSizeThreshold :: Int

  -- | If a continuation variable has an unfolding, it is stored here.
  , inlineCoDefs :: Map CoVar ContDef
  -- | If a function has an unfolding, it is stored here.
  , inlineFnDefs :: Map TmVar FunDef

  -- | Values are bound here, so that beta-redexes can reduce.
  , inlineValDefs :: Map TmVar ValueK

  -- | A substitution on term variables, used when beta-reducing and unfolding.
  , inlineTmSub :: Map TmVar TmVar
  -- | A substitution on term variables, used when beta-reducing and unfolding.
  , inlineCoSub :: Map CoVar CoVar
  }

withTmSub :: (TmVar, TmVar) -> InlineM a -> InlineM a
withTmSub (x, y) m = local f m
  where
    f env = env { inlineTmSub = Map.insert x y (inlineTmSub env) }

withCoSub :: (CoVar, CoVar) -> InlineM a -> InlineM a
withCoSub (x, y) m = local f m
  where
    f env = env { inlineCoSub = Map.insert x y (inlineCoSub env) }

withVal :: TmVar -> ValueK -> InlineM a -> InlineM a
withVal x v m = local f m
  where
    f env = env { inlineValDefs = Map.insert x v (inlineValDefs env) }

withFn :: FunDef -> InlineM a -> InlineM a
withFn fn@(FunDef f _ _ _) m = local g m
  where
    g env = env { inlineFnDefs = Map.insert f fn (inlineFnDefs env) }

withCont :: ContDef -> InlineM a -> InlineM a
withCont kont@(ContDef k _ _) m = local g m
  where
    g env = env { inlineCoDefs = Map.insert k kont (inlineCoDefs env) }

appTmSub :: TmVar -> InlineM TmVar
appTmSub x = do
  env <- ask
  case Map.lookup x (inlineTmSub env) of
    Nothing -> pure x
    Just y -> pure y

appCoSub :: CoVar -> InlineM CoVar
appCoSub k = do
  env <- ask
  case Map.lookup k (inlineCoSub env) of
    Nothing -> pure k
    Just k' -> pure k'

-- | Inline definitions and simplify redexes.
inlineK :: TermK -> InlineM TermK
-- Occurrences get inlined if their definition is in the environment.
-- (TODO: Inline decision based on context of occurrence, not just context of
-- definition?)
inlineK (JumpK k x) = do
  env <- ask
  case Map.lookup k (inlineCoDefs env) of
    Nothing -> pure (JumpK k x)
    Just (ContDef _ y e) -> withTmSub (y, x) $ inlineK e
inlineK (CallK f x k) = do
  env <- ask
  case Map.lookup f (inlineFnDefs env) of
    Nothing -> pure (CallK f x k)
    Just (FunDef _ y k' e) -> withCoSub (k', k) $ withTmSub (y, x) $ inlineK e
-- Eliminators use 'inlineValDefs' to beta-reduce, if possible.
-- (A function parameter will not reduce, e.g.)
inlineK (CaseK x k1 k2) = do
  x' <- appTmSub x
  env <- ask
  case Map.lookup x' (inlineValDefs env) of
    Just (InlK y) -> inlineK (JumpK k1 y)
    Just (InrK y) -> inlineK (JumpK k2 y)
    Just _ -> error "case on non-inj value"
    Nothing -> pure (CaseK x' k1 k2)
inlineK (LetFstK x y e) = do
  y' <- appTmSub y
  env <- ask
  -- We need to rebuild the LetFstK here because there still might be some
  -- variable that refers to it.
  -- TODO: Use usage information to discard dead bindings.
  case Map.lookup y' (inlineValDefs env) of
    Just (PairK p _) -> LetFstK x y' <$> withTmSub (x, p) (inlineK e)
    Just _ -> error "fst on non-pair value"
    Nothing -> LetFstK x y' <$> inlineK e
inlineK (LetSndK x y e) = do
  y' <- appTmSub y
  env <- ask
  -- We need to rebuild the LetFstK here because there still might be some
  -- variable that refers to it.
  -- A DCE pass can remove it later.
  case Map.lookup y' (inlineValDefs env) of
    Just (PairK _ q) -> LetSndK x y' <$> withTmSub (x, q) (inlineK e)
    Just _ -> error "snd on non-pair value"
    Nothing -> LetFstK x y' <$> inlineK e
-- Functions and continuations are the things that need to be inlined.
-- These two cases decide whether or not a binding should be added to the environment.
-- When extending the environment:
-- * take a census (count how many occurrences of the bound variable, while
--   also reducing beta-redexes on the way)
-- * If 0 occurrences (after reduction), discard.
-- * If 1 occurrence, always inline
-- * If >1 occurrence, inline if small
--   (Or if would reduce? Maybe census collects argument patterns instead)
-- TODO: This is still incorrect if the binding is self-recursive.
-- TODO: Use loop-breakers to inline recursive bind groups.
inlineK (LetContK ks e) = case ks of
  [] -> inlineK e
  [k] -> LetContK ks <$> withCont k (inlineK e)
  _ -> LetContK ks <$> inlineK e
inlineK (LetFunK fs e) = case fs of
  [] -> inlineK e
  [f] -> LetFunK fs <$> withFn f (inlineK e)
  _ -> LetFunK fs <$> inlineK e
-- Value bindings are added to 'inlineValDefs', so they can be reduced.
inlineK (LetValK x v e) = LetValK x v <$> withVal x v (inlineK e)

-- Secrets of GHC Inliner:
-- data Usage = LoopBreaker | Dead | OnceSafe | MultiSafe | OnceUnsafe | MultiUnsafe
data Usage
  -- variable occurs zero times in body
  = Unused
  -- variable occurs up to once in all paths. (e.g., once on one path, never on the other)
  -- (Actually, does this make sense when considering case-continuations?)
  | AffineUsage
  -- variable occurs more than once
  | ManyUsage

-- | Count occurrences and pick loop breakers, annotating binders with usage
-- information.
-- TODO: Can't really return a map of usage information because it might shadow.
-- Need to annotate binders.
-- countOccurrences :: TermK -> (TermK, Map TmVar Usage, Map CoVar Usage)
-- countOccurrences e = (_, _, _)

-- TODO: Count occurrences of covariables as well.
-- countOccurrences :: Map TmVar ValueK -> Set TmVar -> TermK -> (TermK, Map TmVar Int)
-- If y in vs, that's an occurrence.
-- If y := (p, q) in env, substitute x := p, discard let x = fst y.
-- countOccurrences vs (LetFstK x y e) = _

-- Count number of 'let' bindings, recursively.
sizeK :: TermK -> Int
sizeK (LetFunK fs e) = sum (map (\ (FunDef f x k e') -> sizeK e') fs) + sizeK e
sizeK (LetValK x v e) = 1 + sizeK e


-- Higher-order functions can be eliminated using monomorphization
-- (I don't think I need this, because I can do closures+function pointers)




-- Closure conversion:
-- https://gist.github.com/jozefg/652f1d7407b7f0266ae9
--
-- Example:
-- let a = 4; b = 3; in let f = \x -> \y -> a*x + b*y in f 2 5
-- let a = 4; b = 3; in
--   let
--     f = <{a := a, b := b}, \x -> <{a := a, b := b, x = x}, \y -> a*x + b*y>>;
--   in
--     f 2 5

-- Note: [Closure Conversion and Lifting]
-- After closure conversion, every lambda is annotated with its free variables.
-- If there are no free variables, the lambda can be trivially lifted to the top level.
-- If there are free variables, [Selective Lambda Lifting.pdf] can optionally
-- lift if it would be beneficial.
-- However, not all closures can/should be lifted. For example, consider a
-- lambda in a loop, that captures a different value of 'n' each time.
--
-- For compilation, there is still some "hoisting" that needs to be done,
-- because the code pointer for each lambda needs to be defined at the top
-- level, and also because the struct for the captured variables needs to be
-- hoisted too.

-- cconvTy :: TypeK -> TypeC
-- cconvTy (a -> b) = ∃c. (c -> cconvTy a -> cconvTy b) × c
-- (actually, CPS types rather than a -> b, but approximately.)
-- (Also, this version tends to have lots of fst/snd from nested pairs. Could
-- do n-ary tuples instead.)

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC TmVar ValueC TermC -- let x = v in e, allocation
  | LetFstC TmVar TmVar TermC -- let x = fst y in e, projection
  | LetFunC [ClosureDef] TermC
  | LetContC [ContClosureDef] TermC
  | JumpC CoVar TmVar -- k x
  -- Invoke a closure by providing a value for the only remaining argument.
  | CallC FnName TmVar CoVar -- f x k
  | CaseC TmVar CoVar CoVar -- case x of k1 | k2

-- | @f {x+, k+} y k = e@
-- TODO: Closures can capture functions as well.
data ClosureDef = ClosureDef FnName [TmVar] [CoVar] TmVar CoVar TermC

-- | @k {x+, k+} y = e@
data ContClosureDef = ContClosureDef CoVar [TmVar] [CoVar] TmVar TermC

data ValueC
  = PairC TmVar TmVar
  | InlC TmVar
  | InrC TmVar
  | NilC

fv :: TermK -> (Set TmVar, Set CoVar)
fv (JumpK k x) = (Set.singleton x, Set.singleton k)
fv (CallK f x k) = (Set.fromList [f, x], Set.singleton k)
fv (CaseK x k1 k2) = (Set.singleton x, Set.fromList [k1, k2])
fv (LetFstK x y e) = let (tms, cos) = fv e in (Set.insert y (Set.delete x tms), cos)
fv (LetSndK x y e) = let (tms, cos) = fv e in (Set.insert y (Set.delete x tms), cos)
fv (LetValK x v e) = let (tms, cos) = fv e in fv' v <> (Set.delete x tms, cos)
fv (LetFunK fs e) = let (tms, cos) = fv e in foldMap fvFunDef fs <> (tms, cos)
fv (LetContK ks e) = let (tms, cos) = fv e in foldMap fvContDef ks <> (tms, cos Set.\\ bound)
  where bound = foldMap (\ (ContDef k _ _) -> Set.singleton k) ks

fv' :: ValueK -> (Set TmVar, Set CoVar)
fv' NilK = (Set.empty, Set.empty)
fv' (PairK x y) = (Set.fromList [x, y], Set.empty)
fv' (InlK x) = (Set.singleton x, Set.empty)
fv' (InrK x) = (Set.singleton x, Set.empty)

fvFunDef :: FunDef -> (Set TmVar, Set CoVar)
fvFunDef (FunDef f x k e) = let (tms, cos) = fv e in (Set.delete x tms, Set.delete k cos)

fvContDef :: ContDef -> (Set TmVar, Set CoVar)
fvContDef (ContDef k x e) = let (tms, cos) = fv e in (Set.delete x tms, cos)

-- TODO: Recursive occurrences count as free variables, because they need to be
-- present in the closure environment.
cconv :: TermK -> TermC
cconv (LetFunK fs e) = LetFunC (map ann fs) (cconv e)
  where
    ann fun@(FunDef (TmVar f) x k e) =
      let (tms, cos) = fvFunDef fun in
      ClosureDef (FnName f) (Set.toList tms) (Set.toList cos) x k (cconv e)
cconv (LetContK ks e) = LetContC (map ann ks) (cconv e)
  where
    ann kont@(ContDef k x e) =
      let (tms, cos) = fvContDef kont in
      ContClosureDef k (Set.toList tms) (Set.toList cos) x (cconv e)
cconv (JumpK k x) = JumpC k x
cconv (CallK (TmVar f) x k) = CallC (FnName f) x k
cconv (LetFstK x y e) = LetFstC x y (cconv e)

-- What does well-typed closure conversion look like?
-- How are the values in a closure bound?

-- Closure conversion is not lambda lifting.
-- CC involves capturing the environment when a function is created (but the
-- call site remains mostly the same), LL requires altering the call sites.
-- (LL is O(n^3) or O(n^2), CC is less?)
-- https://pages.github.ccs.neu.edu/jhemann/21SP-CS4400/FAQ/closure-conv/



data TopDecl
  = TopFun [FunDecl]
  | TopCont [ContDecl]

data FunDecl
  -- TODO: Use C names, not TmVar/CoVar/FnName.
  -- TODO: Include number of required locals slots
  = FunDecl FnName CapturedVars TmVar CoVar TermH

data ContDecl
  -- TODO: Include number of required locals slots
  = ContDecl CoVar CapturedVars TmVar TermH

-- Local function and continuation bindings do not have code; they only
-- reference the top-level bindings that do have code.
--
-- Invariant: the LHS of an allocation statement should be a 'CLocal'
data TermH
  = LetValH (CName 'CLocal) ValueH TermH
  | LetPrimH (CName 'CLocal) PrimOp TermH
  -- Should fst and snd be special constructs or primitives?
  -- Maybe constructs, if I extend to n-ary products.
  | forall p. LetFstH (CName 'CLocal) (CName p) TermH
  | forall p q. JumpH (CName p) (CName q)
  | forall p q r. CallH (CName p) (CName q) (CName r)
  | forall p q r. CaseH (CName p) (CName q) (CName r)
  -- Function and continuation closures may be mutually recursive.
  | AllocFun [FunAlloc] TermH
  | AllocCont [ContAlloc] TermH

data ValueH
  = IntValH Int32

data PrimOp
  = forall p q. PrimAddInt32 (CName p) (CName q)
  | forall p q. PrimSubInt32 (CName p) (CName q)
  | forall p q. PrimMulInt32 (CName p) (CName q)

data FunAlloc
  -- Create a closure by providing all the function, continuation, and value
  -- arguments it closes over.
  -- I think that closing over FnName should only occur in a recursive
  -- situation. Bind groups should preferably be minimized before that.
  = FunAlloc FnName CapturedVars -- TODO: (var, CName) pairs? or just [CName]?

data ContAlloc
  = ContAlloc CoVar CapturedVars

data CName :: CPlace -> * where
  LocalName :: CSort -> String -> CName 'CLocal
  EnvRef :: CSort -> String -> CName 'CEnvRef

data CSort = CFun | CCont | CValue

data CPlace = CEnvRef | CLocal

data SomeCName = forall p. SomeCName (CName p)

instance Show (CName p) where
  show (LocalName _ x) = x
  show (EnvRef _ x) = "env->" ++ x


newtype HoistM a = HoistM { runHoistM :: Writer [TopDecl] a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadWriter [TopDecl] HoistM

-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
--
-- Return a list of bind groups.
--
-- (Hmm. This is a bottom-up traversal, I think.)
-- TODO: I need to make sure function and continuation names are globally
-- unique, so I can hoist them without conflicts.
hoist :: TermC -> HoistM TermH
hoist (LetFstC x y e) = do
  x' <- pure x -- TODO: rename 'x' doesn't shadow anything, extend context
  y' <- pure y -- TODO: Use context to convert y :: TmVar into y' :: exists p. CName p 
  e' <- hoist e
  pure (LetFstH x y e')
hoist (LetFunC fs e) = do
  e' <- hoist e
  (fs', ds') <- fmap unzip $ for fs $ \ (ClosureDef f ks xs x k body) -> do
    body' <- hoist body
    pure _
  tell ds' -- TODO: This may be in the wrong order. If so, use 'Dual [TopDecl]'
  pure (AllocFun fs' e')


newtype CapturedVars = CapturedVars [CName 'CEnvRef]

data FunNames
  = FunNames {
    funEnvName :: String
  , funAllocName :: String
  , funCodeName :: String
  , funTraceName :: String
  }

namesForFun :: FnName -> FunNames
namesForFun (FnName f) =
  FunNames {
    funEnvName = f ++ "_env"
  , funAllocName = "allocate_" ++ f ++ "_env"
  , funCodeName = f ++ "_code"
  , funTraceName = "trace_" ++ f ++ "_env"
  }

emitFunEnv :: FunNames -> CapturedVars -> [String]
emitFunEnv ns (CapturedVars xs) =
  ["struct " ++ funEnvName ns ++ " {"] ++
  map mkField xs ++
  ["}"]
  where
    mkField :: CName 'CEnvRef -> String
    mkField (EnvRef CFun f) = "    struct fun *" ++ show f ++ ";"
    mkField (EnvRef CCont k) = "    struct cont *" ++ show k ++ ";"
    mkField (EnvRef CValue x) = "    struct value *" ++ show x ++ ";"

emitFunTrace :: FunNames -> CapturedVars -> [String]
emitFunTrace ns (CapturedVars xs) =
  ["void " ++ funTraceName ns ++ "(void *envp) {"
  ,"    struct " ++ funEnvName ns ++ " *env = envp;"] ++
  map traceField xs ++
  ["}"]
  where
    traceField :: CName 'CEnvRef -> String
    traceField (EnvRef CFun f) = "    trace_fun(env->" ++ f ++ ");"
    traceField (EnvRef CCont k) = "    trace_cont(env->" ++ k ++ ");"
    traceField (EnvRef CValue x) = "    trace_value(env->" ++ x ++ ");"

emitFunCode :: FunNames -> TmVar -> CoVar -> TermH -> [String]
emitFunCode ns x k e =
  ["void " ++ funCodeName ns ++ "(void *envp, struct value *" ++ show x ++ ", struct cont *" ++ show k ++ ") {"
  ,"    struct " ++ funEnvName ns ++ " *env = envp"] ++
  -- TODO: Allocate locals.
  emitFunBody ns e ++
  ["}"]

emitFunBody :: FunNames -> TermH -> [String]
emitFunBody ns (LetValH x (IntValH i) e) =
  ["    struct value *" ++ show x ++ " = allocate_int32(" ++ show i ++");"] ++
  emitFunBody ns e
emitFunBody ns (LetPrimH x p e) =
  ["    struct value *" ++ show x ++ " = " ++ emitPrimOp p ++ ";"] ++
  emitFunBody ns e
emitFunBody ns (JumpH k x) =
  ["    JUMP(" ++ show k ++ ", " ++ show x ++ ");"]

emitPrimOp :: PrimOp -> String
-- TODO: I need to do different things when I reference the environment
-- (env->x) versus use the argument (x).
emitPrimOp (PrimAddInt32 x y) = "prim_addint32(" ++ show x ++ ", " ++ show y ++ ")"

-- emitFunDecl :: FunDecl -> [String]
-- emitFunDecl (FunDecl FnName [FnName] [CoVar] [TmVar] TmVar CoVar TermH) = _
  -- Env, allocate, trace, code.

