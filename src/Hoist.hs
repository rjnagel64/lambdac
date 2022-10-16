{-# LANGUAGE
    StandaloneDeriving
  , DerivingStrategies
  , GeneralizedNewtypeDeriving
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

-- | Hoisting serves two purposes: to split local closure definitions into
-- top-level code declarations and local closure allocations, and to perform
-- miscellaneous C-lowering details like calling conventions and type info
-- values.
--
-- Perhaps the latter task might be better suited to another pass. Hmm.
module Hoist
    ( TermH(..)
    , CaseKind(..)
    , Projection(..)
    , ValueH(..)
    , PrimOp(..)
    , Sort(..)
    , ClosureTele(..)
    , TeleEntry(..)
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
    , closureDeclName
    , closureDeclType
    , ClosureParam(..)
    , ClosureArg(..)
    , EnvDecl(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , EnvAllocArg(..)

    , hoistProgram
    , pprintProgram
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)
import Control.Monad.State

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
--
-- Hmm. Right now, @InfoPlace (Id "aa")@ beasically means `aa : info aa`. Aside
-- from muddling term/info and type namespaces, it also overlaps with
-- InfoPlace2 (denoting `i : info t`.
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
-- At least, that's how I think it should be. So far, I've been turning tyvar
-- binds into info bindings and ignoring the hoist-level tyvar bindings,
-- because they do not impact code generation. The type-checker, however, cares
-- more.

-- TODO: Be principled about CC.TyVar <-> Hoist.TyVar conversions
data TyVar = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa) = aa

asTyVar :: C.TyVar -> TyVar
asTyVar (C.TyVar aa) = TyVar aa

-- | 'ClosureName's are used to refer to top-level functions and continuations.
-- They are introduced by (hoisting) function/continuation closure bindings,
-- and used when allocating function/continuation closures.
newtype ClosureName = ClosureName String
  deriving (Eq, Ord)

instance Show ClosureName where
  show (ClosureName d) = d

asClosureName :: C.Name -> ClosureName
asClosureName (C.Name x i) = ClosureName (x ++ show i)



-- | A 'Sort' describes the runtime layout of a value. It is static information.
data Sort
  = AllocH TyVar
  | IntegerH
  | BooleanH
  | UnitH
  | SumH
  | ProductH Sort Sort
  | ListH Sort
  | ClosureH ClosureTele
  deriving Eq -- Needed for Hoist.TypeCheck.equalSorts

-- It's a bit unfortunate, but I do need to have separate telescopes for
-- parameters and types. The difference is that parameters need names for each
-- value, but closure types ignore value parameter names, and also cannot infer
-- those names.
newtype ClosureTele = ClosureTele [TeleEntry]

instance Eq ClosureTele where
  (==) = equalTele

equalTele :: ClosureTele -> ClosureTele -> Bool
-- Should probably hand-roll, because alpha-equality
equalTele (ClosureTele tele) (ClosureTele tele') = tele == tele'

data TeleEntry
  = ValueTele Sort
  | TypeTele TyVar
  deriving Eq -- Should probably hand-roll, because alpha-equality

closureThunkType :: ClosureTele -> ThunkType
closureThunkType (ClosureTele ss) = ThunkType (map f ss)
  where
    f (ValueTele s) = ThunkValueArg s
    f (TypeTele aa) = ThunkInfoArg -- Hmm. type args aren't really info args, though.

sortOf :: C.Sort -> Sort
sortOf C.Integer = IntegerH
sortOf C.Boolean = BooleanH
sortOf C.Unit = UnitH
sortOf C.Sum = SumH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.List t) = ListH (sortOf t)
sortOf (C.Closure ss) = ClosureH (ClosureTele (map f ss))
  where
    f (C.ValueTele s) = ValueTele (sortOf s)
    f (C.TypeTele aa) = TypeTele (asTyVar aa)
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


data ClosureDecl
  = ClosureDecl ClosureName (Id, EnvDecl) [ClosureParam] TermH

closureDeclName :: ClosureDecl -> ClosureName
closureDeclName (ClosureDecl c _ _ _) = c 

closureDeclType :: ClosureDecl -> ThunkType
closureDeclType (ClosureDecl _ _ params _) = ThunkType (map f params)
  where
    f (PlaceParam p) = ThunkValueArg (placeSort p)
    f (TypeParam i) = ThunkInfoArg

-- TODO: EnvDecl should use InfoPlace2
-- Hmm. Maybe EnvDecl should use 'Id' for the fields?
data EnvDecl = EnvDecl [InfoPlace] [(Place, Info)]

data ClosureParam = PlaceParam Place | TypeParam InfoPlace

-- TODO: I don't like OpaqueArg.
-- It is currently necessary because ThunkType:s can have free type variables.
-- An alternate method would be to add a "pseudo-forall" to the thunk type, so
-- that it is closed and the extra info args can be passed up front.
--
-- (This is the "closed thunk types" proposal that I need to write down)
data ClosureArg = ValueArg Name | TypeArg Info | OpaqueArg Name Info

data TermH
  = LetValH Place ValueH TermH
  | LetPrimH Place PrimOp TermH
  -- 'let value x = fst y in e'
  | LetProjectH Place Name Projection TermH
  | HaltH Sort Name Info
  | OpenH Name ThunkType [ClosureArg]
  | CaseH Name CaseKind [Name]
  -- Closures may be mutually recursive, so they are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

-- TODO(eventually): bring back generic case expressions
data CaseKind = CaseBool | CaseSum Sort Sort | CaseList Sort

data Projection = ProjectFst | ProjectSnd

caseKind :: C.CaseKind -> CaseKind
caseKind C.CaseBool = CaseBool
caseKind (C.CaseSum a b) = CaseSum (sortOf a) (sortOf b)
caseKind (C.CaseList a) = CaseList (sortOf a)

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: Place
  , closureDecl :: ClosureName
  , closureEnvPlace :: Id
  , closureEnv :: EnvAlloc
  }

data EnvAlloc
  = EnvAlloc {
    -- Do these really need to be 'Place's, or can they just be 'Id's?
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
--
-- Another thing to consider is that closure sorts can now have type arguments.
-- Is there really a meaningful distinction between a top-level type/info
-- argument and a nested one?
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
    tycode (ClosureH tele) = 'C' : telecode tele
    tycode IntegerH = "V"
    tycode (AllocH _) = "A"
    tycode SumH = "S"
    tycode BooleanH = "B"
    tycode (ProductH s t) = 'Q' : tycode s ++ tycode t
    tycode UnitH = "U"
    tycode (ListH s) = 'L' : tycode s
    telecode (ClosureTele ss) = show (length ss) ++ concatMap entrycode ss
    entrycode (ValueTele s) = tycode s
    entrycode (TypeTele aa) = "J" -- same as 'I', or different?

instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode



-- Hmm. Instead of 'Writer', would an 'Update' monad be applicable here?
newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set ClosureName) (Writer ClosureDecls)) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter ClosureDecls HoistM
deriving newtype instance MonadState (Set ClosureName) HoistM

data HoistEnv = HoistEnv { localScope :: Scope, envScope :: Scope }

data Scope = Scope { scopePlaces :: Map C.Name Place, scopeInfos :: Map TyVar InfoPlace }

newtype ClosureDecls = ClosureDecls [ClosureDecl]

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls


tellClosures :: [ClosureDecl] -> HoistM ()
tellClosures cs = tell (ClosureDecls cs)

collectThunkTypes :: [ClosureDecl] -> Set ThunkType
collectThunkTypes cs = foldMap closureThunkTypes cs
  where
    closureThunkTypes :: ClosureDecl -> Set ThunkType
    closureThunkTypes cd@(ClosureDecl _ _ params _) = Set.insert ty (foldMap paramThunkTypes params)
      where
        ty = closureDeclType cd

    paramThunkTypes :: ClosureParam -> Set ThunkType
    paramThunkTypes (TypeParam _) = Set.empty
    paramThunkTypes (PlaceParam p) = thunkTypesOf (placeSort p)

    thunkTypesOf :: Sort -> Set ThunkType
    thunkTypesOf (AllocH _) = Set.empty
    thunkTypesOf IntegerH = Set.empty
    thunkTypesOf BooleanH = Set.empty
    thunkTypesOf SumH = Set.empty
    thunkTypesOf UnitH = Set.empty
    thunkTypesOf (ClosureH tele) = Set.insert (closureThunkType tele) (teleThunkTypes tele)
    thunkTypesOf (ProductH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (ListH t) = thunkTypesOf t

    teleThunkTypes :: ClosureTele -> Set ThunkType
    -- We are looking for thunk types, so scoping doesn't matter and foldMap is
    -- fine.
    teleThunkTypes (ClosureTele ss) = foldMap entryThunkTypes ss

    entryThunkTypes :: TeleEntry -> Set ThunkType
    entryThunkTypes (ValueTele s) = thunkTypesOf s
    entryThunkTypes (TypeTele aa) = Set.empty


hoistProgram :: TermC -> (TermH, [ClosureDecl], [ThunkType])
hoistProgram srcC =
  let (srcH, ClosureDecls cs) = runHoist (hoist srcC) in
  let ts = Set.toList $ collectThunkTypes cs in
  (srcH, cs, ts)

runHoist :: HoistM a -> (a, ClosureDecls)
runHoist =
  runWriter .
  flip evalStateT Set.empty .
  flip runReaderT emptyEnv .
  runHoistM
  where
    emptyEnv = HoistEnv emptyScope emptyScope
    emptyScope = Scope Map.empty Map.empty


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
hoist :: TermC -> HoistM TermH
hoist (HaltC x) = do
  (x', s) <- hoistVarOccSort x
  i <- infoForSort s
  pure (HaltH s x' i)
hoist (JumpC k xs) = do
  (k', ty) <- hoistCall k
  ys <- hoistArgList xs
  pure (OpenH k' ty ys)
hoist (CallC f xs ks) = do
  (f', ty) <- hoistCall f
  ys <- hoistArgList (xs ++ ks)
  pure (OpenH f' ty ys)
hoist (InstC f ts ks) = do
  (f', ty) <- hoistCall f
  ys <- hoistArgList ks
  ts' <- traverse (infoForSort . sortOf) ts
  pure (OpenH f' ty (map TypeArg ts' ++ ys))
hoist (CaseC x t ks) = do
  x' <- hoistVarOcc x
  let kind = caseKind t
  ks' <- traverse hoistVarOcc ks
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
  hoistClosureAllocs C.funClosureName C.funClosureSort C.funEnvDef fdecls e
hoist (LetContC ks e) = do
  kdecls <- declareClosureNames C.contClosureName ks
  ds' <- traverse hoistContClosure kdecls
  tellClosures ds'
  hoistClosureAllocs C.contClosureName C.contClosureSort C.contEnvDef kdecls e
hoist (LetAbsC fs e) = do
  fdecls <- declareClosureNames C.absClosureName fs
  ds' <- traverse hoistAbsClosure fdecls
  tellClosures ds'
  hoistClosureAllocs C.absClosureName C.absClosureSort C.absEnvDef fdecls e

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

hoistValue :: ValueC -> HoistM ValueH
hoistValue (IntC i) = pure (IntH (fromIntegral i))
hoistValue (BoolC b) = pure (BoolH b)
hoistValue (PairC x y) = (\ (x', i) (y', j) -> PairH i j x' y') <$> hoistVarOccInfo x <*> hoistVarOccInfo y
hoistValue NilC = pure NilH
hoistValue (InlC x) = (\ (x', i) -> InlH i x') <$> hoistVarOccInfo x
hoistValue (InrC x) = (\ (x', i) -> InrH i x') <$> hoistVarOccInfo x
hoistValue EmptyC = pure ListNilH
hoistValue (ConsC x xs) = (\ (x', i) xs' -> ListConsH i x' xs') <$> hoistVarOccInfo x <*> hoistVarOcc xs

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



declareClosureNames :: (a -> C.Name) -> [a] -> HoistM [(ClosureName, a)]
declareClosureNames closureName cs =
  for cs $ \def -> do
    let
      pickName f ds =
        let d = asClosureName f in
        case Set.member d ds of
          False -> (d, Set.insert d ds)
          True -> pickName (C.prime f) ds
    decls <- get
    let (d, decls') = pickName (closureName def) decls
    put decls'
    pure (d, def)

-- | Replace the set of fields and places in the environment, while leaving the
-- set of declaration names intact. This is because inside a closure, all names
-- refer to either a local variable/parameter (a place), a captured variable (a
-- field), or to a closure that has been hoisted to the top level (a decl)
inClosure :: C.EnvDef -> [C.TyVar] -> [(C.Name, C.Sort)] -> HoistM a -> HoistM ((Id, EnvDecl), [ClosureParam], a)
inClosure (C.EnvDef tyfields fields) typlaces places m = do
  -- Because this is a new top-level context, we do not have to worry about shadowing anything.
  -- TODO: This mess of let-bindings can probably be simplified
  let places' = map (\ (x, s) -> (x, asPlace s x)) places
  let typlaces' = map (\aa -> (asTyVar aa, asInfoPlace aa)) typlaces
  let newLocals = Scope (Map.fromList places') (Map.fromList typlaces')
  let params = map (TypeParam . snd) typlaces' ++ map (PlaceParam . snd) places'

  let fields' = map (\ (x, s) -> (x, asPlace s x)) fields
  let tyfields' = map (\aa -> (asTyVar aa, asInfoPlace aa)) tyfields
  let newEnv = Scope (Map.fromList fields') (Map.fromList tyfields')
  let mkFieldInfo' f = infoForSort (placeSort f)
  fieldsWithInfo <- traverse (\ (_, f) -> (,) <$> pure f <*> mkFieldInfo' f) fields'
  -- TODO: Convert tyfields' to [InfoPlace2]
  let envd = EnvDecl (map snd tyfields') fieldsWithInfo

  let replaceEnv _oldEnv = HoistEnv newLocals newEnv
  r <- local replaceEnv m
  envp <- pickEnvironmentName

  pure ((envp, envd), params, r)

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: HoistM Id
pickEnvironmentName = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places infos) = foldMap (Set.singleton . placeName) places <> foldMap (Set.singleton . infoName) infos
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id ("env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

pickEnvironmentPlace :: Id -> HoistM Id
pickEnvironmentPlace (Id cl) = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places infos) = foldMap (Set.singleton . placeName) places <> foldMap (Set.singleton . infoName) infos
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id (cl ++ "_env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

hoistClosureAllocs :: (a -> C.Name) -> (a -> C.Sort) -> (a -> C.EnvDef) -> [(ClosureName, a)] -> TermC -> HoistM TermH
hoistClosureAllocs closureName closureSort closureEnvDef cdecls e = do
  placesForClosureAllocs closureName closureSort cdecls $ \cplaces -> do
    cs' <- for cplaces $ \ (p, d, def) -> do
      env' <- hoistEnvDef (Set.fromList (map (closureName . snd) cdecls)) (closureEnvDef def)
      envPlace <- pickEnvironmentPlace (placeName p)
      pure (ClosureAlloc p d envPlace env')
    e' <- hoist e
    pure (AllocClosure cs' e')

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

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc = fmap fst . hoistVarOccSort

-- | Hoist a variable in call position and compute its thunk type
hoistCall :: C.Name -> HoistM (Name, ThunkType)
hoistCall x = hoistVarOccSort x >>= \case
  (x', ClosureH tele) -> pure (x', closureThunkType tele)
  (_, s) -> error ("called a non-closure: " ++ show x ++ " : " ++ pprintSort s)

-- | Hoist a list of arguments.
hoistArgList :: [C.Name] -> HoistM [ClosureArg]
hoistArgList xs = traverse f xs
  where
    f x = hoistVarOccSort x >>= \case
      (x', AllocH aa) -> OpaqueArg x' <$> infoForTyVar aa
      (x', _) -> pure (ValueArg x')

-- | Hoist a variable occurrence, and also retrieve the @type_info@ that describes it.
hoistVarOccInfo :: C.Name -> HoistM (Name, Info)
hoistVarOccInfo x = do
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

pprintProgram :: (TermH, [ClosureDecl], [ThunkType]) -> String
pprintProgram (srcH, cs, ts) = pprintThunkTypes ts ++ pprintClosures cs ++ pprintTerm 0 srcH

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH _ x _) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (OpenH c _ args) =
  indent n $ intercalate " " (show c : map pprintClosureArg args) ++ ";\n"
pprintTerm n (CaseH x _kind ks) =
  let branches = intercalate " | " (map show ks) in
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
pprintParam (TypeParam i) = '@' : pprintInfo i

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
pprintClosureAlloc n (ClosureAlloc p d _envPlace env) =
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
pprintSort (ClosureH tele) = "closure(" ++ pprintTele tele ++ ")"
pprintSort (AllocH aa) = "alloc(" ++ show aa ++ ")"

pprintTele :: ClosureTele -> String
pprintTele (ClosureTele ss) = intercalate ", " (map f ss)
  where
    f (ValueTele s) = pprintSort s
    f (TypeTele aa) = '@' : show aa
