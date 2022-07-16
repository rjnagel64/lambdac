{-# LANGUAGE
    StandaloneDeriving
  , DerivingStrategies
  , GeneralizedNewtypeDeriving
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

module Hoist
    ( TermH(..)
    , CaseKind(..)
    , Projection(..)
    , ValueH(..)
    , PrimOp(..)
    , Sort(..)
    , Name(..)
    , Info(..)
    , ThunkType(..)
    , ThunkArg(..)
    , thunkTypeCode
    , PlaceName(..)
    , FieldName(..)
    , InfoName(..)
    , DeclName(..)
    , ClosureDecl(..)
    , ClosureParam(..)
    , ClosureArg(..)
    , EnvDecl(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)

    , runHoist
    , ClosureDecls(..)
    , hoist
    , pprintThunkTypes
    , pprintClosures
    , pprintTerm
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)
import Control.Monad.State

import Data.Bifunctor
import Data.Int (Int64)
import Data.Traversable (for, mapAccumL)
import Data.List (intercalate)
import Data.Function (on)

import qualified CC as C
import CC (TermC(..), ValueC(..), ArithC(..), CmpC(..))

-- TODO: The whole PlaceName/FieldName and LocalName/EnvName feels messy
-- Especially because I need to add some form of name capable of referring to type_info.
--
-- * FieldName is not really that useful??
-- * PlaceName gets used for lots of things: parameters, local variables, etc.
-- * LocalName/EnvName: Could I generalize this to 'LocalName String | ProjectField Name String'?
--   If 'ClosureDecl' gives a name to the environment pointer, environment accesses would look like
--   'ProjectField (LocalName "envp") "x"'. I currently only need one level,
--   but it probably would be useful to make "the thing being projected from" a
--   name reference in its own right.
--   Tracing a thunk declaration could also make use of such a type.
--   (maybe I could even do something weird and add a 'CastField Name Sort' ctor to do stuff)

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
-- TODO: Unify PlaceName and FieldName
data PlaceName = PlaceName { placeSort :: Sort, placeName :: String }

data FieldName = FieldName { fieldSort :: Sort, fieldName :: String }

asPlaceName :: C.Sort -> C.Name -> PlaceName
asPlaceName s (C.Name x i) = PlaceName (sortOf s) (x ++ show i)

asFieldName :: C.Sort -> C.Name -> FieldName
asFieldName s (C.Name x i) = FieldName (sortOf s) (x ++ show i)

data InfoName = InfoName { infoName :: String }

asInfoName :: C.TyVar -> InfoName
asInfoName (C.TyVar aa) = InfoName aa


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
  = ClosureDecl DeclName (String, EnvDecl) [ClosureParam] TermH

data EnvDecl = EnvDecl [InfoName] [(FieldName, Info)]

data ClosureParam = PlaceParam PlaceName | TypeParam InfoName

data TermH
  = LetValH PlaceName ValueH TermH
  | LetPrimH PlaceName PrimOp TermH
  -- 'let value x = fst y in e'
  | LetProjectH PlaceName Name Projection TermH
  | HaltH Name Info
  | OpenH Name ThunkType [ClosureArg]
  | CaseH Name CaseKind [(Name, ThunkType)]
  -- Closures may be mutually recursive, so are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

-- TODO: OpaqueArg Name Info
-- This will let me emit proper info for polymorphic arguments.
data ClosureArg = ValueArg Name | TypeArg Info | OpaqueArg Name Info

-- TODO(eventually): bring back generic case expressions
data CaseKind = CaseBool | CaseSum | CaseList

data Projection = ProjectFst | ProjectSnd

caseKind :: C.Sort -> CaseKind
caseKind C.Boolean = CaseBool
caseKind C.Sum = CaseSum
caseKind (C.List _) = CaseList
caseKind s = error ("cannot perform case analysis on sort " ++ show s)

data ClosureAlloc
  = ClosureAlloc {
    -- TODO: Make ClosureAlloc contain a PlaceName for the environment
    closurePlace :: PlaceName
  , closureType :: ThunkType
  , closureDecl :: DeclName
  , closureEnv :: EnvAlloc
  }

data EnvAlloc
  = EnvAlloc {
    envAllocInfoArgs :: [(InfoName, Info)]
  , envAllocFreeArgs :: [(FieldName, Name)]
  , envAllocRecArgs :: [(FieldName, Name)]
  }

data ValueH
  = IntH Int64
  | BoolH Bool
  | PairH Info Info Name Name
  | NilH
  | InlH Info Name
  | InrH Info Name
  | ListNilH
  | ListConsH Info Name Name

data PrimOp
  = PrimAddInt64 Name Name
  | PrimSubInt64 Name Name
  | PrimMulInt64 Name Name
  | PrimNegInt64 Name
  | PrimEqInt64 Name Name
  | PrimNeInt64 Name Name
  | PrimLtInt64 Name Name
  | PrimLeInt64 Name Name
  | PrimGtInt64 Name Name
  | PrimGeInt64 Name Name

-- | A 'Sort' describes the runtime layout of a value. It is static information.
data Sort
  = IntegerH
  | BooleanH
  | UnitH
  | SumH
  | ProductH Sort Sort
  | ListH Sort
  | ClosureH [Sort]
  | AllocH C.TyVar
  deriving (Eq, Ord)

sortOf :: C.Sort -> Sort
sortOf C.Integer = IntegerH
sortOf C.Boolean = BooleanH
sortOf C.Unit = UnitH
sortOf C.Sum = SumH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.List t) = ListH (sortOf t)
sortOf (C.Closure ss) = ClosureH (map sortOf ss)
sortOf (C.Alloc aa) = AllocH aa

-- | 'Info' is used to represent @type_info@ values that are passed at runtime.
-- This is dynamic information.
data Info
  -- @a0@
  = LocalInfo String
  -- @env->b1@
  | EnvInfo String
  -- @int64_info@
  | Int64Info
  -- @bool_info@
  | BoolInfo
  -- @unit_info@
  | UnitInfo
  -- @sum_info@
  | SumInfo
  -- @pair_info@
  | ProductInfo
  -- @closure_info@
  | ClosureInfo
  -- @list_info@
  | ListInfo

instance Show Info where
  show (LocalInfo aa) = '$' : aa
  show (EnvInfo aa) = "$." ++ aa
  show Int64Info = "$int64"
  show BoolInfo = "$bool"
  show UnitInfo = "$unit"
  show SumInfo = "$sum"
  show ProductInfo = "$pair"
  show ClosureInfo = "$closure"
  show ListInfo = "$list"

-- Note: FieldName:s should not be nested? after closure conversion, all names
-- in a definition are either parameters, local temporaries, or environment
-- field references.
--
-- TODO: HoistEnv should map closure names to thunk types
data HoistEnv
  = HoistEnv {
      localPlaces :: Map C.Name PlaceName
    , envPlaces :: Map C.Name FieldName
    , localInfos :: Map C.TyVar InfoName
    , envInfos :: Map C.TyVar InfoName
  }


newtype ClosureDecls = ClosureDecls [ClosureDecl]

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls

-- | A thunk type is a calling convention for closures: the set of arguments
-- that must be provided to open it. This information is used to generate
-- trampolined tail calls.
--
-- Because 'ThunkType' is mostly concerned with the call site, it does not have
-- a binding structure. (Or does it?)
data ThunkType = ThunkType [ThunkArg]

-- TODO: Does this need an 'OpaqueArg' analogue?
data ThunkArg
  = ThunkValueArg Sort
  | ThunkInfoArg

thunkTypeCode :: ThunkType -> String
thunkTypeCode (ThunkType ss) = concatMap argcode ss
  where
    argcode ThunkInfoArg = "I"
    argcode (ThunkValueArg s) = tycode s
    -- This scheme will almost certainly break down as types get fancier.
    tycode :: Sort -> String
    tycode (ClosureH ss) = 'C' : show (length ss) ++ concatMap tycode ss
    tycode IntegerH = "V"
    tycode (AllocH aa) = "A"
    tycode SumH = "S"
    tycode BooleanH = "B"
    tycode (ProductH s t) = 'Q' : tycode s ++ tycode t
    tycode UnitH = "U"
    tycode (ListH s) = 'L' : tycode s

instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode

newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set DeclName) (Writer (ClosureDecls, Set ThunkType))) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter (ClosureDecls, Set ThunkType) HoistM
deriving newtype instance MonadState (Set DeclName) HoistM

runHoist :: HoistM a -> (a, (ClosureDecls, [ThunkType]))
runHoist = second (second Set.toList) . runWriter .  flip evalStateT Set.empty .  flip runReaderT emptyEnv .  runHoistM
  where emptyEnv = HoistEnv mempty mempty mempty mempty

tellClosures :: [ClosureDecl] -> HoistM ()
tellClosures cs = tell (ClosureDecls cs, ts)
  where
    ts = foldMap closureThunkTypes cs

    closureThunkTypes :: ClosureDecl -> Set ThunkType
    closureThunkTypes (ClosureDecl _ _ params _) = Set.insert ty (foldMap paramThunkTypes params)
      where
        ty = ThunkType (map f params)
        f (TypeParam i) = ThunkInfoArg
        f (PlaceParam p) = ThunkValueArg (placeSort p)

    paramThunkTypes :: ClosureParam -> Set ThunkType
    paramThunkTypes (TypeParam _) = Set.empty
    paramThunkTypes (PlaceParam p) = thunkTypesOf (placeSort p)

    thunkTypesOf :: Sort -> Set ThunkType
    thunkTypesOf (AllocH _) = Set.empty
    thunkTypesOf IntegerH = Set.empty
    thunkTypesOf BooleanH = Set.empty
    thunkTypesOf SumH = Set.empty
    thunkTypesOf UnitH = Set.empty
    thunkTypesOf (ClosureH ss) = Set.insert (ThunkType (map ThunkValueArg ss)) (foldMap thunkTypesOf ss)
    thunkTypesOf (ProductH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (ListH t) = thunkTypesOf t


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
hoist :: TermC -> HoistM TermH
hoist (HaltC x) = (\ (x', i) -> HaltH x' i) <$> hoistVarOcc' x
hoist (JumpC k xs) = do
  (ys, ss) <- hoistArgList xs
  OpenH <$> hoistVarOcc k <*> pure (ThunkType (map ThunkValueArg ss)) <*> pure ys
hoist (CallC f xs ks) = do
  (ys, ss) <- hoistArgList (xs ++ ks)
  OpenH <$> hoistVarOcc f <*> pure (ThunkType (map ThunkValueArg ss)) <*> pure ys
hoist (InstC f ts ks) = do
  (ys, ss) <- hoistArgList ks
  -- TODO: It would be better if OpenH looked up the thunk type of the
  -- head, rather than trying to reconstruct it.
  let infoSorts = replicate (length ts) ThunkInfoArg
  let ty = ThunkType (infoSorts ++ map ThunkValueArg ss)
  ts' <- traverse (infoForSort . sortOf) ts
  OpenH <$> hoistVarOcc f <*> pure ty <*> pure (map TypeArg ts' ++ ys)
hoist (CaseC x t ks) = do
  x' <- hoistVarOcc x
  let kind = caseKind t
  ks' <- for ks $ \ (k, C.BranchType ss) -> do
    k' <- hoistVarOcc k
    pure (k', ThunkType (map (ThunkValueArg . sortOf) ss))
  pure $ CaseH x' kind ks'
hoist (LetValC (x, s) v e) = do
  v' <- hoistValue v
  (x', e') <- withPlace x s $ hoist e
  pure $ LetValH x' v' e'
hoist (LetFstC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetProjectH x' y' ProjectFst e')
hoist (LetSndC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetProjectH x' y' ProjectSnd e')
hoist (LetArithC (x, s) op e) = do
  op' <- hoistArith op
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' op' e')
hoist (LetNegateC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' (PrimNegInt64 y') e')
hoist (LetCompareC (x, s) cmp e) = do
  cmp' <- hoistCmp cmp
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' cmp' e')
hoist (LetFunC fs e) = do
  fdecls <- declareClosureNames C.funClosureName fs
  ds' <- traverse hoistFunClosure fdecls
  tellClosures ds'

  placesForClosureAllocs C.funClosureName C.funClosureSort fdecls $ \fplaces -> do
    fs' <- for fplaces $ \ (p, d, C.FunClosureDef _f env xs ks _e) -> do
      env' <- hoistEnvDef env
      let ty = ThunkType ([ThunkValueArg (sortOf s) | (_x, s) <- xs] ++ [ThunkValueArg (sortOf s) | (_k, s) <- ks])
      -- TODO: Give name to environment allocations as well
      pure (ClosureAlloc p ty d env')
    e' <- hoist e
    pure (AllocClosure fs' e')
hoist (LetContC ks e) = do
  kdecls <- declareClosureNames C.contClosureName ks
  ds' <- traverse hoistContClosure kdecls
  tellClosures ds'

  placesForClosureAllocs C.contClosureName C.contClosureSort kdecls $ \kplaces -> do
    ks' <- for kplaces $ \ (p, d, C.ContClosureDef _k env xs _e) -> do
      env' <- hoistEnvDef env
      let ty = ThunkType [ThunkValueArg (sortOf s) | (_x, s) <- xs]
      pure (ClosureAlloc p ty d env')
    e' <- hoist e
    pure (AllocClosure ks' e')
hoist (LetAbsC fs e) = do
  fdecls <- declareClosureNames C.absClosureName fs
  ds' <- traverse hoistAbsClosure fdecls
  tellClosures ds'

  placesForClosureAllocs C.absClosureName C.absClosureSort fdecls $ \fplaces -> do
    fs' <- for fplaces $ \ (p, d, C.AbsClosureDef _f env as ks _e) -> do
      env' <- hoistEnvDef env
      let infoSorts = replicate (length as) ThunkInfoArg
      let ty = ThunkType (infoSorts ++ [ThunkValueArg (sortOf s) | (_k, s) <- ks])
      pure (ClosureAlloc p ty d env')
    e' <- hoist e
    pure (AllocClosure fs' e')

hoistEnvDef :: C.EnvDef -> HoistM EnvAlloc
hoistEnvDef (C.EnvDef tys free rec) =
  EnvAlloc
    <$> traverse envAllocInfo tys
    <*> traverse envAllocField free
    <*> traverse envAllocField rec

envAllocInfo :: C.TyVar -> HoistM (InfoName, Info)
envAllocInfo aa = do
  let info = asInfoName aa
  i <- infoForSort (AllocH aa)
  pure (info, i)

envAllocField :: (C.Name, C.Sort) -> HoistM (FieldName, Name)
envAllocField (x, s) = do
  let field = asFieldName s x
  x' <- hoistVarOcc x
  pure (field, x')


placesForClosureAllocs :: (a -> C.Name) -> (a -> C.Sort) -> [(DeclName, a)] -> ([(PlaceName, DeclName, a)] -> HoistM r) -> HoistM r
placesForClosureAllocs closureName closureSort cdecls kont = do
  HoistEnv scope _ _ _ <- ask
  let
    pickPlace sc (d, def) =
      let (cname, csort) = (closureName def, closureSort def) in
      let c = go sc cname in
      let p = asPlaceName csort c in
      (Map.insert cname p sc, (p, d, def))
    go sc c = case Map.lookup c sc of
      Nothing -> c
      Just _ -> go sc (C.prime c)
  let (scope', cplaces) = mapAccumL pickPlace scope cdecls
  let extend (HoistEnv _ fields iplaces ifields) = HoistEnv scope' fields iplaces ifields
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
hoistValue (IntC i) = pure (IntH (fromIntegral i))
hoistValue (BoolC b) = pure (BoolH b)
hoistValue (PairC x y) = (\ (x', i) (y', j) -> PairH i j x' y') <$> hoistVarOcc' x <*> hoistVarOcc' y
hoistValue NilC = pure NilH
hoistValue (InlC x) = (\ (x', i) -> InlH i x') <$> hoistVarOcc' x
hoistValue (InrC x) = (\ (x', i) -> InrH i x') <$> hoistVarOcc' x
hoistValue EmptyC = pure ListNilH
hoistValue (ConsC x xs) = (\ (x', i) xs' -> ListConsH i x' xs') <$> hoistVarOcc' x <*> hoistVarOcc xs

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
  (env', places', body') <- inClosure env [] (xs ++ ks) $ hoist body
  let fd = ClosureDecl fdecl env' (map PlaceParam places') body'
  pure fd

hoistContClosure :: (DeclName, C.ContClosureDef) -> HoistM ClosureDecl
hoistContClosure (kdecl, C.ContClosureDef _k env xs body) = do
  (env', places', body') <- inClosure env [] xs $ hoist body
  let kd = ClosureDecl kdecl env' (map PlaceParam places') body'
  pure kd

hoistAbsClosure :: (DeclName, C.AbsClosureDef) -> HoistM ClosureDecl
hoistAbsClosure (fdecl, C.AbsClosureDef _f env as ks body) = do
  (env', places', body') <- inClosure env as ks $ hoist body
  let fd = ClosureDecl fdecl env' (map (TypeParam . asInfoName) as ++ map PlaceParam places') body'
  pure fd

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: Set String -> String
pickEnvironmentName sc = go (0 :: Int)
  where
    go i =
      let envp = "env" ++ show i in
      if Set.member envp sc then go (i+1) else envp

-- | Replace the set of fields and places in the environment, while leaving the
-- set of declaration names intact. This is because inside a closure, all names
-- refer to either a local variable/parameter (a place), a captured variable (a
-- field), or to a closure that has been hoisted to the top level (a decl)
inClosure :: C.EnvDef -> [C.TyVar] -> [(C.Name, C.Sort)] -> HoistM a -> HoistM ((String, EnvDecl), [PlaceName], a)
inClosure (C.EnvDef tys free rec) typlaces places m = do
  -- Because this is a new top-level context, we do not have to worry about shadowing anything.
  let fields = free ++ rec
  let fields' = map (\ (x, s) -> (x, asFieldName s x)) fields
  let places' = map (\ (x, s) -> (x, asPlaceName s x)) places
  let tyfields' = map (\aa -> (aa, asInfoName aa)) tys
  let typlaces' = map (\aa -> (aa, asInfoName aa)) typlaces
  let replaceEnv _oldEnv = HoistEnv (Map.fromList places') (Map.fromList fields') (Map.fromList typlaces') (Map.fromList tyfields')
  r <- local replaceEnv m
  -- TODO: consider typlaces in scope when picking environment name.
  let inScopeNames = map (fieldName . snd) fields' ++ map (placeName . snd) places' ++ map (infoName . snd) tyfields' 
  let name = pickEnvironmentName (Set.fromList inScopeNames)

  let mkFieldInfo' f = infoForSort (fieldSort f)
  fieldsWithInfo <- traverse (\ (_, f) -> (,) <$> pure f <*> mkFieldInfo' f) fields'
  pure ((name, EnvDecl (map snd tyfields') fieldsWithInfo), map snd places', r)

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc x = do
  HoistEnv ps fs ips ifs <- ask
  case Map.lookup x ps of
    Just (PlaceName _ x') -> pure (LocalName x')
    Nothing -> case Map.lookup x fs of
      Just (FieldName _ x') -> pure (EnvName x')
      Nothing -> error ("not in scope: " ++ show x)

-- | Hoist a variable occurrence, and also retrieve its sort.
hoistVarOccSort :: C.Name -> HoistM (Name, Sort)
hoistVarOccSort x = do
  HoistEnv ps fs ips ifs <- ask
  case Map.lookup x ps of
    Just (PlaceName s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (FieldName s x') -> pure (EnvName x', s)
      Nothing -> error ("not in scope: " ++ show x)

hoistArgList :: [C.Name] -> HoistM ([ClosureArg], [Sort])
hoistArgList xs = unzip <$> traverse f xs
  where
    f x = hoistVarOccSort x >>= \ (x', s) -> case s of
      AllocH _ -> do
        i <- infoForSort s
        pure (OpaqueArg x' i, s)
      _ -> pure (ValueArg x', s)

-- | Hoist a variable occurrence, and also retrieve the @type_info@ that describes it.
hoistVarOcc' :: C.Name -> HoistM (Name, Info)
hoistVarOcc' x = do
  (x', s) <- hoistVarOccSort x
  s' <- infoForSort s
  pure (x', s')

infoForSort :: Sort -> HoistM Info
infoForSort (AllocH aa) = do
  HoistEnv _ _ iplaces ifields <- ask
  case Map.lookup aa iplaces of
    Just (InfoName aa') -> pure (LocalInfo aa')
    Nothing -> case Map.lookup aa ifields of
      Just (InfoName aa') -> pure (EnvInfo aa')
      Nothing -> error ("not in scope: " ++ show aa)
infoForSort IntegerH = pure Int64Info
infoForSort BooleanH = pure BoolInfo
infoForSort UnitH = pure UnitInfo
infoForSort SumH = pure SumInfo
infoForSort (ProductH _ _) = pure ProductInfo
infoForSort (ListH _) = pure ListInfo
infoForSort (ClosureH _) = pure ClosureInfo

-- | Bind a place name of the appropriate sort, running a monadic action in the
-- extended environment.
withPlace :: C.Name -> C.Sort -> HoistM a -> HoistM (PlaceName, a)
withPlace x s m = do
  x' <- makePlace x s
  let f (HoistEnv places fields iplaces ifields) = HoistEnv (Map.insert x x' places) fields iplaces ifields
  a <- local f m
  pure (x', a)

makePlace :: C.Name -> C.Sort -> HoistM PlaceName
makePlace x s = do
  HoistEnv places _ _ _ <- ask
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
pprintTerm n (HaltH x _) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (OpenH c _ args) =
  indent n $ intercalate " " (show c : map pprintClosureArg args) ++ ";\n"
pprintTerm n (CaseH x _kind ks) =
  let branches = intercalate " | " (map (show . fst) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetValH x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetProjectH x y p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ proj p ++ " " ++ show y ++ ";\n") ++ pprintTerm n e
  where
    proj ProjectFst = "fst"
    proj ProjectSnd = "snd"
pprintTerm n (LetPrimH x p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintPrim p ++ ";\n") ++ pprintTerm n e
pprintTerm n (AllocClosure cs e) =
  indent n "let\n" ++ concatMap (pprintClosureAlloc (n+2)) cs ++ indent n "in\n" ++ pprintTerm n e

pprintClosureArg :: ClosureArg -> String
pprintClosureArg (TypeArg i) = '@' : show i
pprintClosureArg (ValueArg x) = show x
pprintClosureArg (OpaqueArg x i) = show x ++ "@" ++ show i

pprintValue :: ValueH -> String
pprintValue (PairH _ _ x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue NilH = "()"
pprintValue (IntH i) = show i
pprintValue (BoolH b) = if b then "true" else "false"
pprintValue (InlH _ x) = "inl " ++ show x
pprintValue (InrH _ y) = "inr " ++ show y
pprintValue ListNilH = "nil"
pprintValue (ListConsH _ x xs) = "cons " ++ show x ++ " " ++ show xs

pprintPrim :: PrimOp -> String
pprintPrim (PrimAddInt64 x y) = "prim_addint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimSubInt64 x y) = "prim_subint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimMulInt64 x y) = "prim_mulint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimNegInt64 x) = "prim_negint64(" ++ show x ++ ")"
pprintPrim (PrimEqInt64 x y) = "prim_eqint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimNeInt64 x y) = "prim_neint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimLtInt64 x y) = "prim_ltint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimLeInt64 x y) = "prim_leint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimGtInt64 x y) = "prim_gtint64(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimGeInt64 x y) = "prim_geint64(" ++ show x ++ ", " ++ show y ++ ")"

pprintPlace :: PlaceName -> String
pprintPlace (PlaceName s x) = pprintSort s ++ " " ++ x

pprintField :: FieldName -> String
pprintField (FieldName s x) = pprintSort s ++ " " ++ x

pprintInfo :: InfoName -> String
pprintInfo (InfoName aa) = aa

pprintParam :: ClosureParam -> String
pprintParam (PlaceParam p) = pprintPlace p
pprintParam (TypeParam i) = pprintInfo i

pprintClosures :: [ClosureDecl] -> String
pprintClosures cs = "let {\n" ++ concatMap (pprintClosureDecl 2) cs ++ "}\n"

pprintClosureDecl :: Int -> ClosureDecl -> String
pprintClosureDecl n (ClosureDecl f (name, EnvDecl is fs) params e) =
  indent n (show f ++ " " ++ env ++ " (" ++ intercalate ", " (map pprintParam params) ++ ") =\n") ++
  pprintTerm (n+2) e
  where
    env = name ++ " : {" ++ envInfos ++ "; " ++ envFields ++ "}"
    envInfos = intercalate ", " (map pprintInfo is)
    envFields = intercalate ", " (map (pprintField . fst) fs)

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p _t d env) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ pprintEnvAlloc env ++ "\n"

pprintEnvAlloc :: EnvAlloc -> String
pprintEnvAlloc (EnvAlloc info free rec) =
  "{" ++ intercalate ", " (map pprintAllocInfo info ++ map pprintAllocArg (free ++ rec)) ++ "}"

pprintAllocInfo :: (InfoName, Info) -> String
pprintAllocInfo (info, i) = "@" ++ pprintInfo info ++ " = " ++ show i

pprintAllocArg :: (FieldName, Name) -> String
pprintAllocArg (field, x) = pprintField field ++ " = " ++ show x

pprintThunkTypes :: [ThunkType] -> String
pprintThunkTypes ts = unlines (map pprintThunkType ts)
  where
    pprintThunkType :: ThunkType -> String
    pprintThunkType (ThunkType ss) = "thunk (" ++ intercalate ", " (map pprintThunkArg ss) ++ ") -> !"

    pprintThunkArg (ThunkValueArg s) = pprintSort s
    pprintThunkArg ThunkInfoArg = "info"

pprintSort :: Sort -> String
pprintSort IntegerH = "int"
pprintSort BooleanH = "bool"
pprintSort UnitH = "unit"
pprintSort SumH = "sum"
pprintSort (ListH t) = "list " ++ pprintSort t
pprintSort (ProductH t s) = "pair " ++ pprintSort t ++ " " ++ pprintSort s
pprintSort (ClosureH ss) = "closure(" ++ intercalate ", " (map pprintSort ss) ++ ")"
pprintSort (AllocH aa) = "alloc(" ++ show aa ++ ")"
