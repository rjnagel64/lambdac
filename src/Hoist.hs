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
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Int
import Data.Traversable (for, mapAccumL)

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

data Sort = Fun | Cont | Value
  deriving (Eq, Ord)

-- Place names declare a reference to an object: value, function, or continuation.
-- They are used as parameters and also as local temporaries.
data PlaceName = PlaceName Sort String

data FieldName = FieldName Sort String

-- | 'DeclName's are used to refer to top-level functions and continuations.
-- They are introduced by (hoisting) function/continuation closure bingings,
-- and used when allocating function/continuation closures.
newtype DeclName = DeclName String


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
  = FunAlloc DeclName EnvAlloc

data ContAlloc
  = ContAlloc DeclName EnvAlloc

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

-- TODO: Map C.Name DeclName for names that refer to top-level closures.
-- Note: FieldName:s should not be nested? after closure conversion, all names
-- in a definition are either parameters, local temporaries, or environment
-- field references.
data HoistEnv = HoistEnv (Map C.Name PlaceName) (Map C.Name FieldName) (Map C.Name DeclName)


newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (Writer [TopDecl]) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter [TopDecl] HoistM

runHoist :: HoistM a -> (a, [TopDecl])
runHoist = runWriter . flip runReaderT emptyEnv . runHoistM
  where emptyEnv = HoistEnv mempty mempty mempty


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
--
-- Return a list of bind groups.
--
-- TODO: I need to make sure function and continuation names are globally
-- unique, so I can hoist them without conflicts.
hoist :: TermC -> HoistM TermH
hoist (LetValC x v e) = do
  v' <- hoistValue v
  (x', e') <- withPlace x Value $ hoist e
  pure $ LetValH x' v' e'
hoist (LetFstC x y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x Value $ hoist e
  pure (LetFstH x' y' e')
hoist (LetFunC fs e) = do
  (fs', ds', e') <- withClosures (map C.closureName fs) Fun $ do
    (fs', ds') <- fmap unzip $ traverse hoistFunClosure fs
    e' <- hoist e
    pure (fs', ds', e')
  -- TODO: This may be in the wrong order. If so, use 'Dual [TopDecl]'
  tell [TopFun ds']
  pure (AllocFun fs' e')
hoist (JumpC x k) = JumpH <$> hoistVarOcc x <*> hoistVarOcc k

hoistValue :: ValueC -> HoistM ValueH
hoistValue (PairC x y) = PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue (InlC x) = InlH <$> hoistVarOcc x
hoistValue (InrC x) = InrH <$> hoistVarOcc x
hoistValue NilC = pure NilH

-- | Extend the hoisting environment with place names for each closure in a
-- binding group.
withClosures :: [C.Name] -> Sort -> HoistM a -> HoistM a
withClosures xs s m = do
  HoistEnv scope _ _ <- ask
  -- TODO: This name-freshening logic is still a mess.
  let (scope', xs') = mapAccumL pickName scope xs
      pickName sc x = let x' = loop sc x 0 in (Map.insert x x' sc, x')
      loop sc (C.Name x) i = let x' = C.Name (x ++ show i) in case Map.lookup x' sc of
        Nothing -> (PlaceName s (x ++ show i))
        Just _ -> loop sc (C.Name x) (i+1)
  let extendEnv (HoistEnv places fields decls) = HoistEnv scope' fields decls
  local extendEnv m

hoistFunClosure :: C.ClosureDef -> HoistM (FunAlloc, FunDecl)
hoistFunClosure (C.ClosureDef f free rec x k body) = do
  -- Actually, hasn't 'f' been given a top-level name already, because of
  -- hoisting the bind group?
  -- So instead of generating a name, I should be looking up the closure name.
  f' <- lookupClosureName f
  enva <- EnvAlloc <$> traverse hoistVarOcc (free ++ rec)
  let fa = FunAlloc f' enva
  -- TODO: Infer sorts of each field. Fields are captured from in-scope
  -- places, so do that here.
  fields <- traverse inferSort (free ++ rec)
  (fields', places', body') <- inClosure fields [(x, Value), (k, Cont)] $ hoist body
  let envd = EnvDecl fields'
  let [x', k'] = places' -- Safe: inClosure preserves length; inClosure called with 2 places.
  let fd = FunDecl f' envd x' k' body'
  pure (fa, fd)

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
  let replaceEnv (HoistEnv _ _ decls) = HoistEnv (Map.fromList places') (Map.fromList fields') decls
  r <- local replaceEnv m
  pure (map snd fields', map snd places', r)

lookupClosureName :: C.Name -> HoistM DeclName
lookupClosureName f = do
  HoistEnv _ _ decls <- ask
  pure (decls Map.! f)

-- | Infer the sort of a name by looking up what place or field it refers to.
-- TODO: Provide this information as part of closure conversion, rather than
-- needing to infer it.
inferSort :: C.Name -> HoistM (C.Name, Sort)
inferSort x = do
  HoistEnv places fields decls <- ask
  case Map.lookup x places of
    Just (PlaceName s _) -> pure (x, s)
    Nothing -> error "Sort of name unknown" -- Lookup fields? I don't think so.

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc x = do
  HoistEnv ps fs ds <- ask
  case Map.lookup x ps of
    Just (PlaceName _ x') -> pure (LocalName x')
    -- TODO: WRONG. local variables do not refer to decls. They refer to
    -- closures and values, from local scope and the environment.
    Nothing -> case Map.lookup x fs of
      Just (FieldName _ x') -> pure (EnvName x')
      Nothing -> error "not in scope"

-- | Bind a place name of the appropriate sort, running a monadic action in the
-- extended environment.
withPlace :: C.Name -> Sort -> HoistM a -> HoistM (PlaceName, a)
withPlace x s m = do
  x' <- makePlace x s
  let f (HoistEnv places fields decls) = HoistEnv (Map.insert x x' places) fields decls
  a <- local f m
  pure (x', a)

makePlace :: C.Name -> Sort -> HoistM PlaceName
makePlace (C.Name x) s = do
  HoistEnv places _ _ <- ask
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
