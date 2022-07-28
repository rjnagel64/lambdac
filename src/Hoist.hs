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
    , Id(..)
    , TyVar(..)
    , ThunkType(..)
    , ThunkArg(..)
    , thunkTypeCode
    , Place(..)
    , InfoPlace(..)
    , ClosureName(..)
    , ClosureDecl(..)
    , ClosureParam(..)
    , ClosureArg(..)
    , EnvDecl(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , EnvAllocArg(..)

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


-- | An 'Id' is any type of identifier.
newtype Id = Id String
  deriving (Eq, Ord)

instance Show Id where
  show (Id x) = x

-- | A 'Name' refers to a 'Place'. It is either a 'Place' in the local
-- scope, or in the environment scope.
data Name = LocalName Id | EnvName Id
  deriving (Eq, Ord)

instance Show Name where
  show (LocalName x) = show x
  show (EnvName x) = "@." ++ show x

-- | A 'Place' is a location that can hold a value. It has an identifier and a
-- sort that specifies what values can be stored there.
data Place = Place { placeSort :: Sort, placeName :: Id }

asPlace :: C.Sort -> C.Name -> Place
asPlace s (C.Name x i) = Place (sortOf s) (Id (x ++ show i))

-- | A 'InfoPlace' is a location that can hold a @type_info@.
data InfoPlace = InfoPlace { infoName :: Id }

asInfoPlace :: C.TyVar -> InfoPlace
asInfoPlace (C.TyVar aa) = InfoPlace (Id aa)

-- | The /real/ 'InfoPlace'. @InfoPlace2 x s@ denotes an info binding @x : info
-- s@.
-- TODO: Distinguish 'InfoPlace' from 'TyPlace'
data InfoPlace2 = InfoPlace2 { infoName2 :: Id, infoSort2 :: Sort }

-- Note: Part of the confusion between type places and info places is that when
-- translating from CC to Hoist, a CC type variable binding becomes an (erased)
-- type variable binding and a (relevant) info binding.
--
-- At least, that's how I think it should be.


-- TODO: Be principled about CC.TyVar <-> Hoist.TyVar conversions
data TyVar = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa) = aa

asTyVar :: C.TyVar -> TyVar
asTyVar (C.TyVar aa) = TyVar aa


-- | 'DeclName's are used to refer to top-level functions and continuations.
-- They are introduced by (hoisting) function/continuation closure bingings,
-- and used when allocating function/continuation closures.
newtype ClosureName = ClosureName String
  deriving (Eq, Ord)

instance Show ClosureName where
  show (ClosureName d) = d

asDeclName :: C.Name -> ClosureName
asDeclName (C.Name x i) = ClosureName (x ++ show i)


-- Should ClosureDecl contain a ThunkType?
data ClosureDecl
  = ClosureDecl ClosureName (Id, EnvDecl) [ClosureParam] TermH

-- TODO: EnvDecl should use InfoPlace2
data EnvDecl = EnvDecl [InfoPlace] [(Place, Info)]

data ClosureParam = PlaceParam Place | TypeParam InfoPlace

data TermH
  = LetValH Place ValueH TermH
  | LetPrimH Place PrimOp TermH
  -- 'let value x = fst y in e'
  | LetProjectH Place Name Projection TermH
  | HaltH Sort Name Info
  | OpenH Name ThunkType [ClosureArg]
  | CaseH Name CaseKind [(Name, ThunkType)]
  -- Closures may be mutually recursive, so are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

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
    -- TODO: Make ClosureAlloc contain a Place for the environment
    closurePlace :: Place
  , closureDecl :: ClosureName
  , closureEnv :: EnvAlloc
  }

data EnvAlloc
  = EnvAlloc {
    envAllocInfoArgs :: [(InfoPlace, Info)]
  , envAllocValueArgs :: [EnvAllocArg]
  }

data EnvAllocArg
  = EnvFreeArg Place Name
  | EnvRecArg Place Name

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
  -- TODO: Sort.ClosureH should have type/info parameters (It should be a telescope)
  | ClosureH [Sort]
  -- TODO: Sort.Closure should not use CC.TyVar
  | AllocH TyVar
  deriving (Eq, Ord)

sortOf :: C.Sort -> Sort
sortOf C.Integer = IntegerH
sortOf C.Boolean = BooleanH
sortOf C.Unit = UnitH
sortOf C.Sum = SumH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.List t) = ListH (sortOf t)
sortOf (C.Closure ss) = ClosureH (map sortOf ss)
sortOf (C.Alloc aa) = AllocH (asTyVar aa)

-- | 'Info' is used to represent @type_info@ values that are passed at runtime.
-- This is dynamic information.
data Info
  -- @a0@
  = LocalInfo Id
  -- @env->b1@
  | EnvInfo Id
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
  show (LocalInfo aa) = '$' : show aa
  show (EnvInfo aa) = "$." ++ show aa
  show Int64Info = "$int64"
  show BoolInfo = "$bool"
  show UnitInfo = "$unit"
  show SumInfo = "$sum"
  show ProductInfo = "$pair"
  show ClosureInfo = "$closure"
  show ListInfo = "$list"

data HoistEnv = HoistEnv { localScope :: Scope, envScope :: Scope }

data Scope = Scope { scopePlaces :: Map C.Name Place, scopeInfos :: Map TyVar InfoPlace }

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
-- More generally, is a 'Sort' really the right thing to use here?
-- ThunkType/ThunkArg are more for specifying the calling convention, an opaque
-- "this closure expects an integer, an opaque value, and a closure" as
-- arguments rather than the actual details of the argument types.
data ThunkArg
  = ThunkValueArg Sort
  | ThunkInfoArg

thunkTypeCode :: ThunkType -> String
thunkTypeCode (ThunkType ts) = concatMap argcode ts
  where
    argcode ThunkInfoArg = "I"
    argcode (ThunkValueArg s) = tycode s
    -- This scheme will almost certainly break down as types get fancier.
    tycode :: Sort -> String
    tycode (ClosureH ss) = 'C' : show (length ss) ++ concatMap tycode ss
    tycode IntegerH = "V"
    tycode (AllocH _) = "A"
    tycode SumH = "S"
    tycode BooleanH = "B"
    tycode (ProductH s t) = 'Q' : tycode s ++ tycode t
    tycode UnitH = "U"
    tycode (ListH s) = 'L' : tycode s

instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode

-- Hmm. Instead of 'Writer', would an 'Update' monad be applicable here?
newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Map ClosureName ThunkType) (Writer (ClosureDecls, Set ThunkType))) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter (ClosureDecls, Set ThunkType) HoistM
deriving newtype instance MonadState (Map ClosureName ThunkType) HoistM

runHoist :: HoistM a -> (a, (ClosureDecls, [ThunkType]))
runHoist =
  second (second Set.toList) .
  runWriter .
  flip evalStateT Map.empty .
  flip runReaderT emptyEnv .
  runHoistM
  where
    emptyEnv = HoistEnv emptyScope emptyScope
    emptyScope = Scope Map.empty Map.empty

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
hoist (HaltC x) = do
  (x', s) <- hoistVarOccSort x
  i <- infoForSort s
  pure (HaltH s x' i)
hoist (JumpC k xs) = do
  (k', ss) <- hoistCall k
  ys <- hoistArgList xs
  pure (OpenH k' (ThunkType (map ThunkValueArg ss)) ys)
hoist (CallC f xs ks) = do
  (f', ss) <- hoistCall f
  ys <- hoistArgList (xs ++ ks)
  pure (OpenH f' (ThunkType (map ThunkValueArg ss)) ys)
hoist (InstC f ts ks) = do
  (f', ss) <- hoistCall f
  ys <- hoistArgList ks
  let infoSorts = replicate (length ts) ThunkInfoArg
  let ty = ThunkType (infoSorts ++ map ThunkValueArg ss)
  ts' <- traverse (infoForSort . sortOf) ts
  pure (OpenH f' ty (map TypeArg ts' ++ ys))
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
  let funThunkType (C.FunClosureDef _ _ xs ks _) = ThunkType (map (ThunkValueArg . sortOf . snd) xs ++ map (ThunkValueArg . sortOf . snd) ks)
  fdecls <- declareClosureNames C.funClosureName funThunkType fs
  ds' <- traverse hoistFunClosure fdecls
  tellClosures ds'
  hoistClosureAllocs C.funClosureName C.funClosureSort C.funEnvDef fdecls e
hoist (LetContC ks e) = do
  let contThunkType (C.ContClosureDef _ _ xs _) = ThunkType (map (ThunkValueArg . sortOf . snd) xs)
  kdecls <- declareClosureNames C.contClosureName contThunkType ks
  ds' <- traverse hoistContClosure kdecls
  tellClosures ds'
  hoistClosureAllocs C.contClosureName C.contClosureSort C.contEnvDef kdecls e
hoist (LetAbsC fs e) = do
  let absThunkType (C.AbsClosureDef _ _ as ks _) = ThunkType (replicate (length as) ThunkInfoArg ++ map (ThunkValueArg . sortOf . snd) ks)
  fdecls <- declareClosureNames C.absClosureName absThunkType fs
  ds' <- traverse hoistAbsClosure fdecls
  tellClosures ds'
  hoistClosureAllocs C.absClosureName C.absClosureSort C.absEnvDef fdecls e

hoistEnvDef :: Set C.Name -> C.EnvDef -> HoistM EnvAlloc
hoistEnvDef recNames (C.EnvDef tys fields) = do
  tyfields <- traverse envAllocInfo tys
  fields' <- traverse (envAllocField recNames) fields
  pure (EnvAlloc tyfields fields')

envAllocInfo :: C.TyVar -> HoistM (InfoPlace, Info)
envAllocInfo aa = do
  let info = asInfoPlace aa
  -- This is sketchy. Figure out how it should really work.
  i <- infoForTyVar (asTyVar aa)
  pure (info, i)

envAllocField :: Set C.Name -> (C.Name, C.Sort) -> HoistM EnvAllocArg
envAllocField recNames (x, s) = case Set.member x recNames of
  False -> EnvFreeArg (asPlace s x) <$> hoistVarOcc x
  True -> EnvRecArg (asPlace s x) <$> hoistVarOcc x


hoistClosureAllocs :: (a -> C.Name) -> (a -> C.Sort) -> (a -> C.EnvDef) -> [(ClosureName, a)] -> TermC -> HoistM TermH
hoistClosureAllocs closureName closureSort closureEnvDef cdecls e = do
  placesForClosureAllocs closureName closureSort cdecls $ \cplaces -> do
    cs' <- for cplaces $ \ (p, d, def) -> do
      env' <- hoistEnvDef (Set.fromList (map (closureName . snd) cdecls)) (closureEnvDef def)
      -- TODO: Give name to environment allocations as well
      pure (ClosureAlloc p d env')
    e' <- hoist e
    pure (AllocClosure cs' e')

-- TODO: Generate places for environment allocations in placesForClosureAllocs?
-- TODO: Compute thunk types in placesForClosureAllocs?
-- Hmm. The return type here could possibly use a helper type.
placesForClosureAllocs :: (a -> C.Name) -> (a -> C.Sort) -> [(ClosureName, a)] -> ([(Place, ClosureName, a)] -> HoistM r) -> HoistM r
placesForClosureAllocs closureName closureSort cdecls kont = do
  scope <- asks (scopePlaces . localScope)
  let
    pickPlace sc (d, def) =
      let (cname, csort) = (closureName def, closureSort def) in
      let c = go sc cname in
      let p = asPlace csort c in
      (Map.insert cname p sc, (p, d, def))
    go sc c = case Map.lookup c sc of
      Nothing -> c
      Just _ -> go sc (C.prime c)
  let (scope', cplaces) = mapAccumL pickPlace scope cdecls
  let extend (HoistEnv (Scope _ fields) env) = HoistEnv (Scope scope' fields) env
  local extend (kont cplaces)


declareClosureNames :: (a -> C.Name) -> (a -> ThunkType) -> [a] -> HoistM [(ClosureName, a)]
declareClosureNames closureName closureThunkType cs =
  for cs $ \def -> do
    let
      pickName f ds =
        let d = asDeclName f in
        case Map.lookup d ds of
          Nothing -> let ty = closureThunkType def in (d, Map.insert d ty ds)
          Just _ty -> pickName (C.prime f) ds
    decls <- get
    let (d, decls') = pickName (closureName def) decls
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


hoistFunClosure :: (ClosureName, C.FunClosureDef) -> HoistM ClosureDecl
hoistFunClosure (fdecl, C.FunClosureDef _f env xs ks body) = do
  (env', params', body') <- inClosure env [] (xs ++ ks) $ hoist body
  pure (ClosureDecl fdecl env' params' body')

hoistContClosure :: (ClosureName, C.ContClosureDef) -> HoistM ClosureDecl
hoistContClosure (kdecl, C.ContClosureDef _k env xs body) = do
  (env', params', body') <- inClosure env [] xs $ hoist body
  pure (ClosureDecl kdecl env' params' body')

hoistAbsClosure :: (ClosureName, C.AbsClosureDef) -> HoistM ClosureDecl
hoistAbsClosure (fdecl, C.AbsClosureDef _f env as ks body) = do
  (env', params', body') <- inClosure env as ks $ hoist body
  pure (ClosureDecl fdecl env' params' body')

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: Set Id -> Id
pickEnvironmentName sc = go (0 :: Int)
  where
    go i =
      let envp = Id ("env" ++ show i) in
      if Set.member envp sc then go (i+1) else envp

-- | Replace the set of fields and places in the environment, while leaving the
-- set of declaration names intact. This is because inside a closure, all names
-- refer to either a local variable/parameter (a place), a captured variable (a
-- field), or to a closure that has been hoisted to the top level (a decl)
inClosure :: C.EnvDef -> [C.TyVar] -> [(C.Name, C.Sort)] -> HoistM a -> HoistM ((Id, EnvDecl), [ClosureParam], a)
inClosure (C.EnvDef tyfields fields) typlaces places m = do
  -- Because this is a new top-level context, we do not have to worry about shadowing anything.
  let fields' = map (\ (x, s) -> (x, asPlace s x)) fields
  let places' = map (\ (x, s) -> (x, asPlace s x)) places
  let tyfields' = map (\aa -> (asTyVar aa, asInfoPlace aa)) tyfields
  let typlaces' = map (\aa -> (asTyVar aa, asInfoPlace aa)) typlaces
  let newLocals = Scope (Map.fromList places') (Map.fromList typlaces')
  let newEnv = Scope (Map.fromList fields') (Map.fromList tyfields')
  let replaceEnv _oldEnv = HoistEnv newLocals newEnv
  r <- local replaceEnv m
  let inScopeNames = map (placeName . snd) fields' ++ map (placeName . snd) places' ++ map (infoName . snd) tyfields' ++ map (infoName . snd) typlaces'
  let name = pickEnvironmentName (Set.fromList inScopeNames)

  let mkFieldInfo' f = infoForSort (placeSort f)
  fieldsWithInfo <- traverse (\ (_, f) -> (,) <$> pure f <*> mkFieldInfo' f) fields'
  let params = map (TypeParam . snd) typlaces' ++ map (PlaceParam . snd) places'
  -- TODO: Convert tyfields' to [InfoPlace2]
  let envd = EnvDecl (map snd tyfields') fieldsWithInfo
  pure ((name, envd), params, r)

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc x = do
  ps <- asks (scopePlaces . localScope)
  fs <- asks (scopePlaces . envScope)
  case Map.lookup x ps of
    Just (Place _ x') -> pure (LocalName x')
    Nothing -> case Map.lookup x fs of
      Just (Place _ x') -> pure (EnvName x')
      Nothing -> error ("not in scope: " ++ show x)

-- | Hoist a variable occurrence, and also retrieve its sort.
hoistVarOccSort :: C.Name -> HoistM (Name, Sort)
hoistVarOccSort x = do
  ps <- asks (scopePlaces . localScope)
  fs <- asks (scopePlaces . envScope)
  case Map.lookup x ps of
    Just (Place s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (Place s x') -> pure (EnvName x', s)
      Nothing -> error ("not in scope: " ++ show x)

hoistCall :: C.Name -> HoistM (Name, [Sort])
hoistCall x = do
  ps <- asks (scopePlaces . localScope)
  fs <- asks (scopePlaces . envScope)
  (x', s) <- case Map.lookup x ps of
    Just (Place s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (Place s x') -> pure (EnvName x', s)
      Nothing -> error ("not in scope: " ++ show x)
  case s of
    ClosureH ss -> pure (x', ss)
    _ -> error ("called a non-closure: " ++ show x ++ " : " ++ pprintSort s)

hoistArgList :: [C.Name] -> HoistM [ClosureArg]
hoistArgList xs = traverse f xs
  where
    f x = hoistVarOccSort x >>= \ (x', s) -> case s of
      AllocH _ -> do
        i <- infoForSort s
        pure (OpaqueArg x' i)
      _ -> pure (ValueArg x')

-- | Hoist a variable occurrence, and also retrieve the @type_info@ that describes it.
hoistVarOcc' :: C.Name -> HoistM (Name, Info)
hoistVarOcc' x = do
  (x', s) <- hoistVarOccSort x
  s' <- infoForSort s
  pure (x', s')

infoForSort :: Sort -> HoistM Info
infoForSort (AllocH aa) = infoForTyVar aa
infoForSort IntegerH = pure Int64Info
infoForSort BooleanH = pure BoolInfo
infoForSort UnitH = pure UnitInfo
infoForSort SumH = pure SumInfo
infoForSort (ProductH _ _) = pure ProductInfo
infoForSort (ListH _) = pure ListInfo
infoForSort (ClosureH _) = pure ClosureInfo

infoForTyVar :: TyVar -> HoistM Info
infoForTyVar aa = do
  iplaces <- asks (scopeInfos . localScope)
  ifields <- asks (scopeInfos . envScope)
  case Map.lookup aa iplaces of
    Just (InfoPlace aa') -> pure (LocalInfo aa')
    Nothing -> case Map.lookup aa ifields of
      Just (InfoPlace aa') -> pure (EnvInfo aa')
      Nothing -> error ("not in scope: " ++ show aa)

-- | Bind a place name of the appropriate sort, running a monadic action in the
-- extended environment.
withPlace :: C.Name -> C.Sort -> HoistM a -> HoistM (Place, a)
withPlace x s m = do
  x' <- makePlace x s
  let f (HoistEnv (Scope places fields) env) = HoistEnv (Scope (Map.insert x x' places) fields) env
  a <- local f m
  pure (x', a)

makePlace :: C.Name -> C.Sort -> HoistM Place
makePlace x s = do
  places <- asks (scopePlaces . localScope)
  go x places
  where
    -- I think this is fine. We might shadow local names, which is bad, but
    -- environment references are guarded by 'env->'.
    go :: C.Name -> Map C.Name Place -> HoistM Place
    go v ps = case Map.lookup v ps of
      Nothing -> pure (asPlace s v)
      Just _ -> go (C.prime v) ps


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH _ x _) = indent n $ "HALT " ++ show x ++ ";\n"
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

pprintPlace :: Place -> String
pprintPlace (Place s x) = pprintSort s ++ " " ++ show x

pprintInfo :: InfoPlace -> String
pprintInfo (InfoPlace aa) = show aa

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
    env = show name ++ " : {" ++ infoFields ++ "; " ++ valueFields ++ "}"
    infoFields = intercalate ", " (map pprintInfo is)
    valueFields = intercalate ", " (map (pprintPlace . fst) fs)

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d env) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ pprintEnvAlloc env ++ "\n"

pprintEnvAlloc :: EnvAlloc -> String
pprintEnvAlloc (EnvAlloc info fields) =
  "{" ++ intercalate ", " (map pprintAllocInfo info ++ map pprintAllocArg fields) ++ "}"

pprintAllocInfo :: (InfoPlace, Info) -> String
pprintAllocInfo (info, i) = "@" ++ pprintInfo info ++ " = " ++ show i

pprintAllocArg :: EnvAllocArg -> String
pprintAllocArg (EnvFreeArg field x) = pprintPlace field ++ " = " ++ show x
pprintAllocArg (EnvRecArg field x) = pprintPlace field ++ " = " ++ show x

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
