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
    , EnvDecl(..)
    , FunAlloc(..)
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
import CC (TermC(..), ValueC(..))

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

data Sort = Fun | Cont | Value
  deriving (Eq, Ord)

instance Show Sort where
  show Fun = "fun"
  show Cont = "cont"
  show Value = "value"

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
  | JumpH Name Name
  | CallH Name Name Name
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

-- TODO: When allocating an environment, I need to distinguish between names
-- that are bound normally, and names that must be bound cyclically.
newtype EnvAlloc = EnvAlloc [Name]

data ValueH
  = IntValH Int32
  | PairH Name Name
  | InlH Name
  | InrH Name
  | NilH

data PrimOp
  = PrimAddInt32 Name Name
  | PrimSubInt32 Name Name
  | PrimMulInt32 Name Name

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
hoist (JumpC x k) = JumpH <$> hoistVarOcc x <*> hoistVarOcc k
hoist (CallC f x k) = CallH <$> hoistVarOcc f <*> hoistVarOcc x <*> hoistVarOcc k
hoist (LetValC x v e) = do
  v' <- hoistValue v
  (x', e') <- withPlace x Value $ hoist e
  pure $ LetValH x' v' e'
hoist (LetFstC x y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x Value $ hoist e
  pure (LetFstH x' y' e')
hoist (LetFunC fs e) = do
  fdecls <- declareClosureNames fs
  ds' <- traverse hoistFunClosure fdecls

  -- TODO: This may be in the wrong order. If so, use 'Dual [TopDecl]'
  tell [TopFun ds']

  placesForFunAllocs fdecls $ \fplaces -> do
    fs' <- for fplaces $ \ (p, d, C.ClosureDef _f free rec _x _k _e) -> do
      env <- traverse hoistVarOcc (free ++ rec)
      pure (FunAlloc p d (EnvAlloc env))
    e' <- hoist e
    pure (AllocFun fs' e')

placesForFunAllocs :: [(DeclName, C.ClosureDef)] -> ([(PlaceName, DeclName, C.ClosureDef)] -> HoistM a) -> HoistM a
placesForFunAllocs fdecls k = do
  HoistEnv scope _ <- ask
  let
    pickPlace sc (d, def@(C.ClosureDef (C.Name f) _ _ _ _ _)) =
      let p = go sc f 0 in (Map.insert (C.Name f) p sc, (p, d, def))
    go sc f i = case Map.lookup (C.Name (f ++ show i)) sc of
      Nothing -> PlaceName Fun (f ++ show i)
      Just _ -> go sc f (i+1)
  let (scope', fplaces) = mapAccumL pickPlace scope fdecls
  let extend (HoistEnv _ fields) = HoistEnv scope' fields
  local extend (k fplaces)


-- This is actually a generic extend-with-places function.
-- Almost redundant with 'withPlace', but this doesn't return the place name.
withAllocationNames :: [(C.Name, PlaceName)] -> HoistM a -> HoistM a
withAllocationNames xs m = local extend m
  where
    extend (HoistEnv places fields) = HoistEnv (foldr (uncurry Map.insert) places xs) fields

declareClosureNames :: [C.ClosureDef] -> HoistM [(DeclName, C.ClosureDef)]
declareClosureNames fs = for fs $ \def -> do
  let
    (C.Name f) = C.closureName def
    pickName i ds =
      let d = DeclName (f ++ show i) in
      if Set.member d ds then pickName (i+1) ds else (d, Set.insert d ds)
  (d, decls') <- pickName 0 <$> get
  put decls'
  pure (d, def)


hoistValue :: ValueC -> HoistM ValueH
hoistValue (PairC x y) = PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue (InlC x) = InlH <$> hoistVarOcc x
hoistValue (InrC x) = InrH <$> hoistVarOcc x
hoistValue NilC = pure NilH


-- | Extend the hoisting environment with place names for each closure in a
-- binding group.
withClosures :: [C.Name] -> Sort -> HoistM a -> HoistM a
withClosures xs s m = do
  HoistEnv scope _ <- ask
  -- TODO: This name-freshening logic is still a mess.
  let (scope', xs') = mapAccumL pickName scope xs
      pickName sc x = let x' = loop sc x 0 in (Map.insert x x' sc, x')
      loop sc (C.Name x) i = let x' = C.Name (x ++ show i) in case Map.lookup x' sc of
        Nothing -> (PlaceName s (x ++ show i))
        Just _ -> loop sc (C.Name x) (i+1)
  -- ... Hang on, aren't the closures being defined in a bindgroup declarations?
  -- Or maybe it's a declaration/allocation divide again. Decl for the
  -- declaration, place for the allocation/body.
  let extendEnv (HoistEnv places fields) = HoistEnv scope' fields
  local extendEnv m

hoistFunClosure :: (DeclName, C.ClosureDef) -> HoistM FunDecl
hoistFunClosure (fdecl, C.ClosureDef f free rec x k body) = do
  fields <- traverse inferSort (free ++ rec)
  (fields', places', body') <- inClosure fields [(x, Value), (k, Cont)] $ hoist body
  let envd = EnvDecl fields'
  let [x', k'] = places' -- Safe: inClosure preserves length; inClosure called with 2 places.
  let fd = FunDecl fdecl envd x' k' body'
  pure (fd)

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

-- | Infer the sort of a name by looking up what place or field it refers to.
-- TODO: Provide this information as part of closure conversion, rather than
-- needing to infer it.
inferSort :: C.Name -> HoistM (C.Name, Sort)
inferSort x = do
  HoistEnv places fields <- ask
  case Map.lookup x places of
    Just (PlaceName s _) -> pure (x, s)
    Nothing -> error "Sort of name unknown" -- Lookup fields? I don't think so.

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
-- TODO: Properly include the "HALT" continuation, so that this hack doesn't exist.
hoistVarOcc x = if x == C.Name "HALT" then pure (LocalName "HALT") else do
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
    go x i ps =
      let x' = (C.Name (x ++ show i)) in -- TODO: C.prime :: C.Name -> C.Name
      -- I think this is fine. We might shadow local names, which is bad, but
      -- environment references are guarded by 'env->'.
      case Map.lookup x' ps of
        Nothing -> pure (PlaceName s (x ++ show i))
        Just _ -> go x (i+1) ps


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermH -> String
pprintTerm n (JumpH k x) = indent n $ show k ++ " " ++ show x ++ ";\n"
pprintTerm n (CallH f x k) = indent n $ show f ++ " " ++ show x ++ " " ++ show k ++ ";\n"
pprintTerm n (LetValH x v e) =
  indent n ("let " ++ place x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
  where place (PlaceName s x) = show s ++ " " ++ x
pprintTerm n (LetFstH x y e) =
  indent n ("let " ++ place x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
  where place (PlaceName s x) = show s ++ " " ++ x
pprintTerm n (AllocFun fs e) =
  indent n "let\n" ++ concatMap (pprintFunAlloc (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e

pprintValue :: ValueH -> String
pprintValue NilH = "()"
pprintValue (PairH x y) = "(" ++ show x ++ ", " ++ show y ++ ")"

pprintTop :: TopDecl -> String
pprintTop (TopFun fs) = "fun {\n" ++ concatMap (pprintFunDecl 2) fs ++ "}\n"

pprintFunDecl :: Int -> FunDecl -> String
pprintFunDecl n (FunDecl f (EnvDecl fs) x k e) =
  indent n (show f ++ " " ++ env ++ " " ++ place x ++ " " ++ place k ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " (map field fs) ++ "}"

    field (FieldName s x) = show s ++ " " ++ x
    place (PlaceName s x) = show s ++ " " ++ x

pprintFunAlloc :: Int -> FunAlloc -> String
pprintFunAlloc n (FunAlloc p d (EnvAlloc env)) = place p ++ " = " ++ show d ++ " " ++ env'
  where
    place (PlaceName s x) = show s ++ " " ++ x
    env' = "{" ++ intercalate ", " (map show env) ++ "}\n"
