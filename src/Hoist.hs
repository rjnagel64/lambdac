{-# LANGUAGE
    StandaloneDeriving
  , DerivingStrategies
  , GeneralizedNewtypeDeriving
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

module Hoist () where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Int
import Data.Traversable (for)

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
newtype DeclName = DeclName String


data TopDecl
  = TopFun [FunDecl]
  | TopCont [ContDecl]

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
data HoistEnv = HoistEnv (Map C.Name PlaceName) (Map C.Name FieldName)


newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (Writer [TopDecl]) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter [TopDecl] HoistM


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
  (fs', ds', e') <- withClosures (map C.closureName fs) $ do
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

-- TODO: function and continuation bindings bring place names into scope.
withClosures :: [C.Name] -> HoistM a -> HoistM a
withClosures xs m = _

hoistFunClosure :: C.ClosureDef -> HoistM (FunAlloc, FunDecl)
hoistFunClosure (C.ClosureDef f free rec x k body) = do
  f' <- hoistClosureName f
  enva <- EnvAlloc <$> traverse hoistVarOcc (free ++ rec)
  let fa = FunAlloc f' enva
  (fields', (x', (k', body'))) <-
    withFields (free ++ rec) $ withPlace x Value $ withPlace k Cont $ hoist body
  let envd = EnvDecl fields'
  let fd = FunDecl f' envd x' k' body'
  pure (fa, fd)

-- I need sorts for each of these names. I need to preserve that info through
-- closure-conversion. Can I infer the sort from the environment? Technically,
-- yes, because field names are derived from in-scope place names, but that
-- feels rather messy.
withFields :: [C.Name] -> HoistM a -> HoistM ([FieldName], a)
withFields xs m = _

makeField :: C.Name -> HoistM FieldName
makeField x = _

hoistClosureName :: C.Name -> HoistM DeclName
-- TODO: Include Map C.Name DeclName in hoist env.
hoistClosureName f = _

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
      Nothing -> error "not in scope"

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
    go x i ps =
      let v = (LocalName (x ++ show i)) in
      -- I think this is fine. We might shadow local names, which is bad, but
      -- environment references are guarded by 'env->'.
      case Map.lookup _ ps of
        Nothing -> pure _
        Just _ -> go x (i+1) ps
