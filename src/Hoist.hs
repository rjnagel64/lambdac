{-# LANGUAGE
    StandaloneDeriving
  , DerivingStrategies
  , GeneralizedNewtypeDeriving
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

module Hoist
    ( TermH(..)
    , ValueH(..)
    , PrimOp(..)
    , Sort(..)
    , Name(..)
    , PlaceName(..)
    , FieldName(..)
    , DeclName(..)
    , FunDecl(..)
    , ContDecl(..)
    , EnvDecl(..)
    , FunAlloc(..)
    , ContAlloc(..)
    , EnvAlloc(..)
    , TopDecl(..)

    , runHoist
    , hoist
    , pprintTop
    , pprintTerm
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Data.Int
import Data.Traversable (for, mapAccumL)
import Data.List (intercalate)

import qualified CC as C
import CC (TermC(..), ValueC(..), Sort(..))

-- This is only for free occurrences? Binders use a different type for names? Yeah.
-- LocalName is for 'x'
-- EnvName is for 'env->q'
--
-- Local names are bound by places; environment names are bound by fields.
-- (Actually, local/place and env/field are pretty much the same, but place and
-- field have sorts as well)
data Name = LocalName String | EnvName String
  deriving (Eq, Ord)

instance Show Name where
  show (LocalName x) = x
  show (EnvName x) = "@." ++ x

-- Place names declare a reference to an object: value, function, or continuation.
-- They are used as parameters and also as local temporaries.
data PlaceName = PlaceName Sort String

data FieldName = FieldName Sort String

-- | 'DeclName's are used to refer to top-level functions and continuations.
-- They are introduced by (hoisting) function/continuation closure bingings,
-- and used when allocating function/continuation closures.
newtype DeclName = DeclName String
  deriving (Eq, Ord)

instance Show DeclName where
  show (DeclName d) = d


data TopDecl
  = TopFun [FunDecl]
  | TopCont [ContDecl]

-- TODO: Generalize arguments from 1 value + 1 cont to list of places. This is
-- needed for future calling conventions, and also making a pattern match in
-- hoistFunClosure safer.
data FunDecl
  -- TODO: Include or compute number of required local slots
  = FunDecl DeclName EnvDecl PlaceName PlaceName TermH

data ContDecl
  -- TODO: Include or compute number of required local slots
  = ContDecl DeclName EnvDecl PlaceName TermH

newtype EnvDecl = EnvDecl [FieldName]

data TermH
  = LetValH PlaceName ValueH TermH
  | LetPrimH PlaceName PrimOp TermH
  -- fst and snd are built-in constructs, for when I expand to n-ary products
  -- and projections.
  | LetFstH PlaceName Name TermH
  | LetSndH PlaceName Name TermH
  | JumpH Name Name
  | CallH Name Name Name
  | HaltH Name
  | CaseH Name Name Name
  -- Function and continuation closures may be mutually recursive.
  | AllocFun [FunAlloc] TermH
  | AllocCont [ContAlloc] TermH

data FunAlloc
  -- @struct fun *foo_17 = allocate_fun(foo_env(...), foo_code, foo_trace);@
  = FunAlloc { funAllocPlace :: PlaceName, funAllocDecl :: DeclName, funAllocEnv :: EnvAlloc }

data ContAlloc
  -- @struct cont *k_32 = allocate_cont(k_env(...), k_code, k_trace);@
  = ContAlloc { contAllocPlace :: PlaceName, contAllocDecl :: DeclName, contAllocEnv :: EnvAlloc }

newtype EnvAlloc = EnvAlloc [(FieldName, Name)]

data ValueH
  = IntH Int32
  | PairH Name Name
  | InlH Name
  | InrH Name
  | NilH

data PrimOp
  = PrimAddInt32 Name Name
  | PrimSubInt32 Name Name
  | PrimMulInt32 Name Name
  | PrimIsZero32 Name

-- Note: FieldName:s should not be nested? after closure conversion, all names
-- in a definition are either parameters, local temporaries, or environment
-- field references.
data HoistEnv = HoistEnv (Map C.Name PlaceName) (Map C.Name FieldName)


newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set DeclName) (Writer [TopDecl])) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter [TopDecl] HoistM
deriving newtype instance MonadState (Set DeclName) HoistM

runHoist :: HoistM a -> (a, [TopDecl])
runHoist = runWriter . flip evalStateT Set.empty . flip runReaderT emptyEnv . runHoistM
  where emptyEnv = HoistEnv mempty mempty


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
--
-- Return a list of bind groups.
--
-- TODO: I need to make sure function and continuation names are globally
-- unique, so I can hoist them without conflicts.
hoist :: TermC -> HoistM TermH
hoist (HaltC x) = HaltH <$> hoistVarOcc x
hoist (JumpC x k) = JumpH <$> hoistVarOcc x <*> hoistVarOcc k
hoist (CallC f x k) = CallH <$> hoistVarOcc f <*> hoistVarOcc x <*> hoistVarOcc k
hoist (CaseC x k1 k2) = CaseH <$> hoistVarOcc x <*> hoistVarOcc k1 <*> hoistVarOcc k2
hoist (LetValC x v e) = do
  v' <- hoistValue v
  (x', e') <- withPlace x Value $ hoist e
  pure $ LetValH x' v' e'
hoist (LetFstC x y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x Value $ hoist e
  pure (LetFstH x' y' e')
hoist (LetSndC x y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x Value $ hoist e
  pure (LetFstH x' y' e')
hoist (LetIsZeroC x y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x Value $ hoist e
  pure (LetPrimH x' (PrimIsZero32 y') e')
hoist (LetAddC z x y e) = do
  x' <- hoistVarOcc x
  y' <- hoistVarOcc y
  (z', e') <- withPlace z Value $ hoist e
  pure (LetPrimH z' (PrimAddInt32 x' y') e')
hoist (LetFunC fs e) = do
  fdecls <- declareClosureNames fs
  ds' <- traverse hoistFunClosure fdecls

  tell [TopFun ds']

  placesForFunAllocs fdecls $ \fplaces -> do
    fs' <- for fplaces $ \ (p, d, C.FunClosureDef _f free rec _x _k _e) -> do
      env <- traverse envAllocField (free ++ rec)
      pure (FunAlloc p d (EnvAlloc env))
    e' <- hoist e
    pure (AllocFun fs' e')
hoist (LetContC ks e) = do
  kdecls <- declareContClosureNames ks
  ds' <- traverse hoistContClosure kdecls

  tell [TopCont ds']

  placesForContAllocs kdecls $ \kplaces -> do
    ks' <- for kplaces $ \ (p, d, C.ContClosureDef _k free rec _x _e) -> do
      env <- traverse envAllocField (free ++ rec)
      pure (ContAlloc p d (EnvAlloc env))
    e' <- hoist e
    pure (AllocCont ks' e')

envAllocField :: (C.Name, Sort) -> HoistM (FieldName, Name)
envAllocField (C.Name x, s) = do
  let field = FieldName s x
  x' <- hoistVarOcc (C.Name x)
  pure (field, x')


placesForFunAllocs :: [(DeclName, C.FunClosureDef)] -> ([(PlaceName, DeclName, C.FunClosureDef)] -> HoistM a) -> HoistM a
placesForFunAllocs fdecls k = do
  HoistEnv scope _ <- ask
  let
    pickPlace sc (d, def@(C.FunClosureDef (C.Name f) _ _ _ _ _)) =
      let p = go sc f (0 :: Int) in (Map.insert (C.Name f) p sc, (p, d, def))
    go sc f i = case Map.lookup (C.Name (f ++ show i)) sc of
      Nothing -> PlaceName Fun (f ++ show i)
      Just _ -> go sc f (i+1)
  let (scope', fplaces) = mapAccumL pickPlace scope fdecls
  let extend (HoistEnv _ fields) = HoistEnv scope' fields
  local extend (k fplaces)

placesForContAllocs :: [(DeclName, C.ContClosureDef)] -> ([(PlaceName, DeclName, C.ContClosureDef)] -> HoistM a) -> HoistM a
placesForContAllocs kdecls k = do
  HoistEnv scope _ <- ask
  let
    pickPlace sc (d, def@(C.ContClosureDef (C.Name defk) _ _ _ _)) =
      let p = go sc defk (0 :: Int) in (Map.insert (C.Name defk) p sc, (p, d, def))
    go sc j i = case Map.lookup (C.Name (j ++ show i)) sc of
      Nothing -> PlaceName Cont (j ++ show i)
      Just _ -> go sc j (i+1)
  let (scope', kplaces) = mapAccumL pickPlace scope kdecls
  let extend (HoistEnv _ fields) = HoistEnv scope' fields
  local extend (k kplaces)


declareClosureNames :: [C.FunClosureDef] -> HoistM [(DeclName, C.FunClosureDef)]
declareClosureNames fs = for fs $ \def -> do
  let
    (C.Name f) = C.funClosureName def
    pickName i ds =
      let d = DeclName (f ++ show i) in
      if Set.member d ds then pickName (i+1) ds else (d, Set.insert d ds)
  (d, decls') <- pickName (0 :: Int) <$> get
  put decls'
  pure (d, def)

declareContClosureNames :: [C.ContClosureDef] -> HoistM [(DeclName, C.ContClosureDef)]
declareContClosureNames fs = for fs $ \def -> do
  let
    (C.Name f) = C.contClosureName def
    pickName i ds =
      let d = DeclName (f ++ show i) in
      if Set.member d ds then pickName (i+1) ds else (d, Set.insert d ds)
  (d, decls') <- pickName (0 :: Int) <$> get
  put decls'
  pure (d, def)


hoistValue :: ValueC -> HoistM ValueH
hoistValue (PairC x y) = PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue (InlC x) = InlH <$> hoistVarOcc x
hoistValue (InrC x) = InrH <$> hoistVarOcc x
hoistValue NilC = pure NilH
hoistValue (IntC i) = pure (IntH (fromIntegral i))


hoistFunClosure :: (DeclName, C.FunClosureDef) -> HoistM FunDecl
hoistFunClosure (fdecl, C.FunClosureDef _f free rec x k body) = do
  let fields = free ++ rec
  (fields', places', body') <- inClosure fields [(x, Value), (k, Cont)] $ hoist body
  let envd = EnvDecl fields'
  let [x', k'] = places' -- Safe: inClosure preserves length; inClosure called with 2 places.
  let fd = FunDecl fdecl envd x' k' body'
  pure fd

hoistContClosure :: (DeclName, C.ContClosureDef) -> HoistM ContDecl
hoistContClosure (kdecl, C.ContClosureDef _k free rec x body) = do
  let fields = free ++ rec
  (fields', places', body') <- inClosure fields [(x, Value)] $ hoist body
  let envd = EnvDecl fields'
  let [x'] = places' -- Safe: inClosure preserves length; inClosure called with 1 place.
  let kd = ContDecl kdecl envd x' body'
  pure kd

-- | Replace the set of fields and places in the environment, while leaving the
-- set of declaration names intact. This is because inside a closure, all names
-- refer to either a local variable/parameter (a place), a captured variable (a
-- field), or to a closure that has been hoisted to the top level (a decl)
inClosure :: [(C.Name, Sort)] -> [(C.Name, Sort)] -> HoistM a -> HoistM ([FieldName], [PlaceName], a)
inClosure fields places m = do
  -- Because this is a new top-level context, we do not have to worry about shadowing anything.
  let places' = map (\ (x@(C.Name x'), s) -> (x, PlaceName s x')) places
  let fields' = map (\ (x@(C.Name x'), s) -> (x, FieldName s x')) fields
  -- Preserve 'DeclName's?
  let replaceEnv (HoistEnv _ _) = HoistEnv (Map.fromList places') (Map.fromList fields')
  r <- local replaceEnv m
  pure (map snd fields', map snd places', r)

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc x = do
  HoistEnv ps fs <- ask
  case Map.lookup x ps of
    Just (PlaceName _ x') -> pure (LocalName x')
    -- TODO: WRONG. local variables do not refer to decls. They refer to
    -- closures and values, from local scope and the environment.
    Nothing -> case Map.lookup x fs of
      Just (FieldName _ x') -> pure (EnvName x')
      Nothing -> error ("not in scope: " ++ show x)

-- | Bind a place name of the appropriate sort, running a monadic action in the
-- extended environment.
withPlace :: C.Name -> Sort -> HoistM a -> HoistM (PlaceName, a)
withPlace x s m = do
  x' <- makePlace x s
  let f (HoistEnv places fields) = HoistEnv (Map.insert x x' places) fields
  a <- local f m
  pure (x', a)

makePlace :: C.Name -> Sort -> HoistM PlaceName
makePlace (C.Name x) s = do
  HoistEnv places _ <- ask
  go x (0 :: Int) places
  where
    go :: String -> Int -> Map C.Name PlaceName -> HoistM PlaceName
    go v i ps =
      let v' = (C.Name (v ++ show i)) in -- TODO: C.prime :: C.Name -> C.Name
      -- I think this is fine. We might shadow local names, which is bad, but
      -- environment references are guarded by 'env->'.
      case Map.lookup v' ps of
        Nothing -> pure (PlaceName s (v ++ show i))
        Just _ -> go v (i+1) ps


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH x) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (JumpH k x) = indent n $ show k ++ " " ++ show x ++ ";\n"
pprintTerm n (CallH f x k) = indent n $ show f ++ " " ++ show x ++ " " ++ show k ++ ";\n"
pprintTerm n (CaseH x k1 k2) =
  indent n $ "case " ++ show x ++ " of " ++ show k1 ++ " | " ++ show k2 ++ ";\n"
pprintTerm n (LetValH x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFstH x y e) =
  indent n ("let " ++ pprintPlace x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndH x y e) =
  indent n ("let " ++ pprintPlace x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetPrimH x p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintPrim p ++ ";\n") ++ pprintTerm n e
pprintTerm n (AllocFun fs e) =
  indent n "let\n" ++ concatMap (pprintFunAlloc (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (AllocCont ks e) =
  indent n "let\n" ++ concatMap (pprintContAlloc (n+2)) ks ++ indent n "in\n" ++ pprintTerm n e

pprintValue :: ValueH -> String
pprintValue NilH = "()"
pprintValue (PairH x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntH i) = show i
pprintValue (InlH x) = "inl " ++ show x
pprintValue (InrH y) = "inr " ++ show y

pprintPrim :: PrimOp -> String
pprintPrim (PrimAddInt32 x y) = "prim_addint32(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimSubInt32 x y) = "prim_subint32(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimMulInt32 x y) = "prim_mulint32(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimIsZero32 x) = "prim_iszero32(" ++ show x ++ ")"

pprintPlace :: PlaceName -> String
pprintPlace (PlaceName s x) = show s ++ " " ++ x

pprintField :: FieldName -> String
pprintField (FieldName s x) = show s ++ " " ++ x

pprintTop :: TopDecl -> String
pprintTop (TopFun fs) = "fun {\n" ++ concatMap (pprintFunDecl 2) fs ++ "}\n"
pprintTop (TopCont ks) = "cont {\n" ++ concatMap (pprintContDecl 2) ks ++ "}\n"

pprintFunDecl :: Int -> FunDecl -> String
pprintFunDecl n (FunDecl f (EnvDecl fs) x k e) =
  indent n (show f ++ " " ++ env ++ " " ++ pprintPlace x ++ " " ++ pprintPlace k ++ " =\n") ++
  pprintTerm (n+2) e
  where env = "{" ++ intercalate ", " (map pprintField fs) ++ "}"

pprintContDecl :: Int -> ContDecl -> String
pprintContDecl n (ContDecl k (EnvDecl fs) x e) =
  indent n (show k ++ " " ++ env ++ " " ++ pprintPlace x ++ " =\n") ++ pprintTerm (n+2) e
  where env = "{" ++ intercalate ", " (map pprintField fs) ++ "}"

pprintFunAlloc :: Int -> FunAlloc -> String
pprintFunAlloc n (FunAlloc p d (EnvAlloc env)) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ env'
  where env' = "{" ++ intercalate ", " (map pprintAllocArg env) ++ "}\n"

pprintContAlloc :: Int -> ContAlloc -> String
pprintContAlloc n (ContAlloc p d (EnvAlloc env)) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ env'
  where env' = "{" ++ intercalate ", " (map pprintAllocArg env) ++ "}\n"

pprintAllocArg :: (FieldName, Name) -> String
pprintAllocArg (field, x) = pprintField field ++ " = " ++ show x
