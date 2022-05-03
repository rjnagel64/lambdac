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
    , ThunkType(..)
    , PlaceName(..)
    , FieldName(..)
    , DeclName(..)
    , ClosureDecl(..)
    , EnvDecl(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)

    , runHoist
    , ClosureDecls(..)
    , hoist
    , pprintClosures
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
import CC (TermC(..), ValueC(..), ArithC(..), CmpC(..), Sort(..), ThunkType(..))

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
data PlaceName = PlaceName { placeSort :: Sort, placeName :: String }

data FieldName = FieldName { fieldSort :: Sort, fieldName :: String }

asPlaceName :: Sort -> C.Name -> PlaceName
asPlaceName s (C.Name x i) = PlaceName s (x ++ show i)

asFieldName :: Sort -> C.Name -> FieldName
asFieldName s (C.Name x i) = FieldName s (x ++ show i)


-- | 'DeclName's are used to refer to top-level functions and continuations.
-- They are introduced by (hoisting) function/continuation closure bingings,
-- and used when allocating function/continuation closures.
newtype DeclName = DeclName String
  deriving (Eq, Ord)

instance Show DeclName where
  show (DeclName d) = d

asDeclName :: C.Name -> DeclName
asDeclName (C.Name x i) = DeclName (x ++ show i)


data ClosureDecl
  = ClosureDecl DeclName EnvDecl [PlaceName] TermH

newtype EnvDecl = EnvDecl [FieldName]

data TermH
  = LetValH PlaceName ValueH TermH
  | LetPrimH PlaceName PrimOp TermH
  -- fst and snd are built-in constructs, for when I expand to n-ary products
  -- and projections.
  | LetFstH PlaceName Name TermH
  | LetSndH PlaceName Name TermH
  | HaltH Name
  | OpenH Name [(Name, Sort)] -- Open a closure, by providing a list of arguments and their sorts.
  | CaseH Name [(Name, ThunkType)]
  -- Closures may be mutually recursive, so are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: PlaceName
  , closureType :: ThunkType
  , closureDecl :: DeclName
  , closureEnv :: EnvAlloc
  }

data EnvAlloc
  = EnvAlloc { envAllocFreeArgs :: [(FieldName, Name)], envAllocRecArgs :: [(FieldName, Name)] }

data ValueH
  = IntH Int64
  | BoolH Bool
  | PairH Name Name
  | InlH Name
  | InrH Name
  | NilH

data PrimOp
  = PrimAddInt64 Name Name
  | PrimSubInt64 Name Name
  | PrimMulInt64 Name Name
  | PrimEqInt64 Name Name
  | PrimNeInt64 Name Name
  | PrimLtInt64 Name Name
  | PrimLeInt64 Name Name
  | PrimGtInt64 Name Name
  | PrimGeInt64 Name Name

-- Note: FieldName:s should not be nested? after closure conversion, all names
-- in a definition are either parameters, local temporaries, or environment
-- field references.
data HoistEnv = HoistEnv (Map C.Name PlaceName) (Map C.Name FieldName)


newtype ClosureDecls = ClosureDecls [ClosureDecl]

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls

newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set DeclName) (Writer ClosureDecls)) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter ClosureDecls HoistM
deriving newtype instance MonadState (Set DeclName) HoistM

runHoist :: HoistM a -> (a, ClosureDecls)
runHoist = runWriter .  flip evalStateT Set.empty .  flip runReaderT emptyEnv .  runHoistM
  where emptyEnv = HoistEnv mempty mempty

tellClosures :: [ClosureDecl] -> HoistM ()
tellClosures cs = tell (ClosureDecls cs)


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
hoist :: TermC -> HoistM TermH
hoist (HaltC x) = HaltH <$> hoistVarOcc x
hoist (JumpC k xs) = OpenH <$> hoistVarOcc k <*> traverse hoistJumpArg xs
hoist (CallC f xs ks) = OpenH <$> hoistVarOcc f <*> traverse hoistJumpArg (xs ++ ks)
hoist (CaseC x ks) = do
  x' <- hoistVarOcc x
  ks' <- for ks $ \ (k, s) -> do
    k' <- hoistVarOcc k
    pure (k', s)
  pure $ CaseH x' ks'
hoist (LetValC (x, s) v e) = do
  v' <- hoistValue v
  (x', e') <- withPlace x s $ hoist e
  pure $ LetValH x' v' e'
hoist (LetFstC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetFstH x' y' e')
hoist (LetSndC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetSndH x' y' e')
hoist (LetArithC (x, s) op e) = do
  op' <- hoistArith op
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' op' e')
hoist (LetCompareC (x, s) cmp e) = do
  cmp' <- hoistCmp cmp
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' cmp' e')
hoist (LetFunC fs e) = do
  fdecls <- declareClosureNames C.funClosureName fs
  ds' <- traverse hoistFunClosure fdecls

  tellClosures ds'

  placesForClosureAllocs C.funClosureName fdecls $ \fplaces -> do
    fs' <- for fplaces $ \ (p, d, C.FunClosureDef _f env xs ks _e) -> do
      env' <- hoistEnvDef env
      let ty = ThunkType ([s | (_x, s) <- xs] ++ [s | (_k, s) <- ks])
      pure (ClosureAlloc p ty d env')
    e' <- hoist e
    pure (AllocClosure fs' e')
hoist (LetContC ks e) = do
  kdecls <- declareClosureNames C.contClosureName ks
  ds' <- traverse hoistContClosure kdecls

  tellClosures ds'

  placesForClosureAllocs C.contClosureName kdecls $ \kplaces -> do
    ks' <- for kplaces $ \ (p, d, C.ContClosureDef _k env xs _e) -> do
      env' <- hoistEnvDef env
      let ty = ThunkType [s | (_x, s) <- xs]
      pure (ClosureAlloc p ty d env')
    e' <- hoist e
    pure (AllocClosure ks' e')

hoistEnvDef :: C.EnvDef -> HoistM EnvAlloc
hoistEnvDef (C.EnvDef free rec) = do
  free' <- traverse envAllocField free
  rec' <- traverse envAllocField rec
  pure (EnvAlloc free' rec')

envAllocField :: (C.Name, Sort) -> HoistM (FieldName, Name)
envAllocField (x, s) = do
  let field = asFieldName s x
  x' <- hoistVarOcc x
  pure (field, x')


placesForClosureAllocs :: (a -> C.Name) -> [(DeclName, a)] -> ([(PlaceName, DeclName, a)] -> HoistM r) -> HoistM r
placesForClosureAllocs closureName cdecls kont = do
  HoistEnv scope _ <- ask
  let
    pickPlace sc (d, def) =
      let cname = closureName def in
      let p = go sc cname in (Map.insert cname p sc, (p, d, def))
    go sc c = case Map.lookup c sc of
      Nothing -> asPlaceName Closure c
      Just _ -> go sc (C.prime c)
  let (scope', cplaces) = mapAccumL pickPlace scope cdecls
  let extend (HoistEnv _ fields) = HoistEnv scope' fields
  local extend (kont cplaces)


declareClosureNames :: (a -> C.Name) -> [a] -> HoistM [(DeclName, a)]
declareClosureNames closureName cs =
  for cs $ \def -> do
    let
      pickName f ds =
        let d = asDeclName f in
        if Set.member d ds then pickName (C.prime f) ds else (d, Set.insert d ds)
    (d, decls') <- pickName (closureName def) <$> get
    put decls'
    pure (d, def)


hoistValue :: ValueC -> HoistM ValueH
hoistValue (PairC x y) = PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue (InlC x) = InlH <$> hoistVarOcc x
hoistValue (InrC x) = InrH <$> hoistVarOcc x
hoistValue NilC = pure NilH
hoistValue (IntC i) = pure (IntH (fromIntegral i))
hoistValue (BoolC b) = pure (BoolH b)

hoistArith :: ArithC -> HoistM PrimOp
hoistArith (AddC x y) = PrimAddInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (SubC x y) = PrimSubInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (MulC x y) = PrimMulInt64 <$> hoistVarOcc x <*> hoistVarOcc y

hoistCmp :: CmpC -> HoistM PrimOp
hoistCmp (EqC x y) = PrimEqInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (NeC x y) = PrimNeInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (LtC x y) = PrimLtInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (LeC x y) = PrimLeInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (GtC x y) = PrimGtInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (GeC x y) = PrimGeInt64 <$> hoistVarOcc x <*> hoistVarOcc y


hoistFunClosure :: (DeclName, C.FunClosureDef) -> HoistM ClosureDecl
hoistFunClosure (fdecl, C.FunClosureDef _f env xs ks body) = do
  (fields', places', body') <- inClosure env (xs ++ ks) $ hoist body
  let envd = EnvDecl fields'
  let fd = ClosureDecl fdecl envd places' body'
  pure fd

hoistContClosure :: (DeclName, C.ContClosureDef) -> HoistM ClosureDecl
hoistContClosure (kdecl, C.ContClosureDef _k env xs body) = do
  (fields', places', body') <- inClosure env xs $ hoist body
  let envd = EnvDecl fields'
  let kd = ClosureDecl kdecl envd places' body'
  pure kd

-- | Replace the set of fields and places in the environment, while leaving the
-- set of declaration names intact. This is because inside a closure, all names
-- refer to either a local variable/parameter (a place), a captured variable (a
-- field), or to a closure that has been hoisted to the top level (a decl)
inClosure :: C.EnvDef -> [(C.Name, Sort)] -> HoistM a -> HoistM ([FieldName], [PlaceName], a)
inClosure (C.EnvDef free rec) places m = do
  -- Because this is a new top-level context, we do not have to worry about shadowing anything.
  let fields = free ++ rec
  let fields' = map (\ (x, s) -> (x, asFieldName s x)) fields
  let places' = map (\ (x, s) -> (x, asPlaceName s x)) places
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
    Nothing -> case Map.lookup x fs of
      Just (FieldName _ x') -> pure (EnvName x')
      Nothing -> error ("not in scope: " ++ show x)

hoistJumpArg :: C.Name -> HoistM (Name, Sort)
hoistJumpArg x = do
  HoistEnv ps fs <- ask
  case Map.lookup x ps of
    Just (PlaceName s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (FieldName s x') -> pure (EnvName x', s)
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
makePlace x s = do
  HoistEnv places _ <- ask
  go x places
  where
    -- I think this is fine. We might shadow local names, which is bad, but
    -- environment references are guarded by 'env->'.
    go :: C.Name -> Map C.Name PlaceName -> HoistM PlaceName
    go v ps = case Map.lookup v ps of
      Nothing -> pure (asPlaceName s v)
      Just _ -> go (C.prime v) ps


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH x) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (OpenH c xs) = indent n $ show c ++ " " ++ intercalate " " (map (show . fst) xs) ++ ";\n"
pprintTerm n (CaseH x ks) =
  let branches = intercalate " | " (map (show . fst) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetValH x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFstH x y e) =
  indent n ("let " ++ pprintPlace x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndH x y e) =
  indent n ("let " ++ pprintPlace x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetPrimH x p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintPrim p ++ ";\n") ++ pprintTerm n e
pprintTerm n (AllocClosure cs e) =
  indent n "let\n" ++ concatMap (pprintClosureAlloc (n+2)) cs ++ indent n "in\n" ++ pprintTerm n e

pprintValue :: ValueH -> String
pprintValue NilH = "()"
pprintValue (PairH x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntH i) = show i
pprintValue (BoolH b) = if b then "true" else "false"
pprintValue (InlH x) = "inl " ++ show x
pprintValue (InrH y) = "inr " ++ show y

pprintPrim :: PrimOp -> String
pprintPrim (PrimAddInt64 x y) = "prim_addint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimSubInt64 x y) = "prim_subint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimMulInt64 x y) = "prim_mulint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimEqInt64 x y) = "prim_eqint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimNeInt64 x y) = "prim_neint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimLtInt64 x y) = "prim_ltint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimLeInt64 x y) = "prim_leint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimGtInt64 x y) = "prim_gtint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimGeInt64 x y) = "prim_geint64(" ++ show x ++ ", " ++ show y ++ ")"

pprintPlace :: PlaceName -> String
pprintPlace (PlaceName s x) = show s ++ " " ++ x

pprintField :: FieldName -> String
pprintField (FieldName s x) = show s ++ " " ++ x

pprintClosures :: [ClosureDecl] -> String
pprintClosures cs = "let {\n" ++ concatMap (pprintClosureDecl 2) cs ++ "}\n"

pprintClosureDecl :: Int -> ClosureDecl -> String
pprintClosureDecl n (ClosureDecl f (EnvDecl fs) params e) =
  indent n (show f ++ " " ++ env ++ " (" ++ intercalate ", " (map pprintPlace params) ++ ") =\n") ++
  pprintTerm (n+2) e
  where env = "{" ++ intercalate ", " (map pprintField fs) ++ "}"

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p _t d (EnvAlloc free rec)) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ env'
  where env' = "{" ++ intercalate ", " (map pprintAllocArg (free ++ rec)) ++ "}\n"

pprintAllocArg :: (FieldName, Name) -> String
pprintAllocArg (field, x) = pprintField field ++ " = " ++ show x
