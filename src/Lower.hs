
-- | A module describing the structure and syntactic operations on the Lower IR.
module Lower
    ( Id(..)
    , Name(..)
    , Place(..)
    , TyVar(..)
    , CodeLabel(..)
    , FieldLabel(..)

    , Sort(..)
    , ClosureTele(..)
    , TeleEntry(..)
    , TyConApp(..)
    , asTyConApp
    , fromTyConApp

    , Kind(..)

    , Subst
    , singleSubst
    , listSubst
    , lookupSubst
    , substSort
    , substTele

    , EnvDecl(..)
    , CodeDecl(..)
    , codeDeclName
    , codeDeclTele
    , ClosureParam(..)

    , DataDecl(..)
    , TyCon(..)
    , CtorDecl(..)
    , Ctor(..)

    , TermH(..)
    , Projection(..)
    , ClosureArg(..)
    , CaseAlt(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , ValueH(..)
    , CtorAppH(..)
    , PrimOp(..)
    , PrimIO(..)

    , lowerProgram

    , Program(..)
    , Decl(..)
    , pprintProgram
    , pprintSort
    , pprintKind

    , ThunkType(..)
    , ThunkArg(..)
    , teleThunkType
    , thunkTypeCode
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Bifunctor
import Data.Function (on)
import Data.Int (Int64)
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import Data.Traversable (for)

import qualified Hoist.IR as H

import Control.Monad.Reader


-- TODO: Avoid shadowing names when preparing to Emit
-- C does not permit multiple variables with the same name. Therefore, before I
-- invoke the Emit phase, I need to ensure that all parameters, local
-- variables, and the environment pointer are distinct.
--
-- Right now, I do this in Hoist and it creates a mess. I want to move it here,
-- where things are better structured and also push the invariant closer to the
-- phase that requires that invariant.


insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs


lowerProgram :: H.Program -> Program
lowerProgram (H.Program ds e) = runM $ do
  lowerDecls ds $ \ds' -> do
    e' <- lowerTerm e
    pure (Program ds' e')

-- Lower a sequence of declarations, where each declaration is in scope for all
-- subsequent ones.
lowerDecls :: [H.Decl] -> ([Decl] -> M a) -> M a
lowerDecls [] k = k []
lowerDecls (H.DeclData dd : ds) k = do
  withDataDecl dd $ \dd' -> do
    lowerDecls ds $ \ds' -> do
      k (DeclData dd' : ds')
lowerDecls (H.DeclCode cd : ds) k = do
  (ed', cd') <- lowerCodeDecl cd
  lowerDecls ds $ \ds' -> do
    k (DeclEnv ed' : DeclCode cd' : ds')

-- withCodeDecl :: H.CodeDecl -> (EnvDecl -> CodeDecl -> M a) -> M a
-- withCodeDecl (H.CodeDecl l (envName, H.EnvDecl aas fields) params body) k = do
--   _

lowerCodeDecl :: H.CodeDecl -> M (EnvDecl, CodeDecl)
lowerCodeDecl (H.CodeDecl l (envName, H.EnvDecl aas fields) params body) = do
  withEnvironment (envName, H.EnvDecl aas fields) $ \aas' envName' fields' -> do
    withParams params $ \params' -> do
      withCodeLabel l $ \l' envTyCon -> do
        body' <- lowerTerm body
        let envd = EnvDecl envTyCon fields'
        let coded = CodeDecl l' aas' (envName', envTyCon) params' body'
        pure (envd, coded)

withEnvironment :: (H.Id, H.EnvDecl) -> ([(TyVar, Kind)] -> Id -> [(Id, Sort)] -> M a) -> M a
withEnvironment (envName, H.EnvDecl aas fields) k = do
  withTyVars aas $ \aas' -> do
    withEnvPtr envName $ \envName' -> do
      withEnvFields envName' fields $ \fields' -> do
        k aas' envName' fields'

withEnvFields :: Id -> [(H.Id, H.Sort)] -> ([(Id, Sort)] -> M a) -> M a
withEnvFields envp fields k = do
  (fields', binds, thunkBindsMaybe) <- fmap unzip3 $ for fields $ \ (x, s) -> do
    x' <- lowerId x
    s' <- lowerSort s
    let field' = (x', s')
    let bind = (H.EnvName x, EnvName envp x')
    case s' of
      ClosureH tele -> do
        let thunkBind = (H.EnvName x, teleThunkType tele)
        pure (field', bind, Just thunkBind)
      _ -> do
        pure (field', bind, Nothing)
  let thunkBinds = catMaybes thunkBindsMaybe
  let extend env = env { envNames = insertMany binds (envNames env), envThunkTypes = insertMany thunkBinds (envThunkTypes env) }
  local extend $ k fields'

withDataDecl :: H.DataDecl -> (DataDecl -> M a) -> M a
withDataDecl (H.DataDecl tc ki cds) k = do
  withTyCon tc $ \tc' -> do
    withCtorDecls tc' (zip [0..] cds) $ \cds' -> do
      k (DataDecl tc' cds')

withCtorDecls :: TyCon -> [(Int, H.CtorDecl)] -> ([CtorDecl] -> M a) -> M a
withCtorDecls _ [] k = k []
withCtorDecls tc' (cd : cds) k =
  withCtorDecl tc' cd $ \cd' -> do
    withCtorDecls tc' cds $ \cds' -> do
      k (cd' : cds')

withCtorDecl :: TyCon -> (Int, H.CtorDecl) -> (CtorDecl -> M a) -> M a
withCtorDecl tc' (i, H.CtorDecl c tys xs) k = do
  withCtor tc' i c $ \c' -> do
    cd <- withTyVars tys $ \tys' -> do
      xs' <- traverse (\ (l, s) -> (,) <$> lowerId l <*> lowerSort s) xs
      pure (CtorDecl c' tys' xs')
    k cd

lowerId :: H.Id -> M Id
lowerId (H.Id x) = pure (Id x)

-- TODO: use an environment lookup here
lowerCodeLabel :: H.CodeLabel -> M CodeLabel
lowerCodeLabel (H.CodeLabel l) = pure (CodeLabel l)

-- TODO: use an environment lookup here
-- (I can't currently because a code label from one code decl needs to be in
-- scope for all subsequent decls, but the scoping needs to be adjusted to make
-- that happen.)
lookupEnvTyCon :: H.CodeLabel -> M TyCon
lookupEnvTyCon l@(H.CodeLabel x) = do
  let tc = TyCon (x ++ "_env")
  pure tc
  -- env <- asks envEnvTyCons
  -- case Map.lookup l env of
  --   Nothing -> error ("code label not in scope: " ++ show l ++ " not in " ++ show env)
  --   Just tc -> pure tc

lowerFieldLabel :: H.FieldLabel -> M FieldLabel
lowerFieldLabel (H.FieldLabel f) = pure (FieldLabel f)

lowerTerm :: H.TermH -> M TermH
lowerTerm (H.HaltH s x) = HaltH <$> lowerSort s <*> lowerName x
lowerTerm (H.OpenH f xs) =
  OpenH <$> lookupThunkType f <*> lowerName f <*> traverse lowerClosureArg xs
lowerTerm (H.IfH x k1 k2) = do
  x' <- lowerName x
  ty1 <- lookupThunkType k1
  k1' <- lowerName k1
  ty2 <- lookupThunkType k2
  k2' <- lowerName k2
  pure (IntCaseH x' [(0, ty1, k1'), (1, ty2, k2')])
lowerTerm (H.CaseH x H.CaseBool ks) = do
  let desc = Map.fromList [(H.Ctor "false", 0), (H.Ctor "true", 1)]
  x' <- lowerName x
  ks' <- for ks $ \ (c, k) -> do
    i <- case Map.lookup c desc of
      Nothing -> error "bad branch in if-statement"
      Just i -> pure i
    ty <- lookupThunkType k
    k' <- lowerName k
    pure (i, ty, k')
  pure (IntCaseH x' ks')
lowerTerm (H.CaseH x (H.TyConApp tc ss) ks) = do
  CaseH <$> lowerName x <*> (TyConApp <$> lowerTyCon tc <*> traverse lowerSort ss) <*> traverse lowerCaseAlt ks
lowerTerm (H.LetValH p v e) = do
  v' <- lowerValue v
  withPlace p $ \p' -> do
    e' <- lowerTerm e
    pure (LetValH p' v' e')
lowerTerm (H.LetPrimH p op e) = do
  op' <- lowerPrimOp op
  withPlace p $ \p' -> do
    e' <- lowerTerm e
    pure (LetPrimH p' op' e')
lowerTerm (H.LetBindH ps px op e) = do
  op' <- lowerIOPrimOp op
  withPlace ps $ \ps' -> do
    withPlace px $ \px' -> do
      e' <- lowerTerm e
      pure (LetBindH ps' px' op' e')
lowerTerm (H.LetProjectH p x proj e) = do
  x' <- lowerName x
  proj' <- lowerProjection proj
  withPlace p $ \p' -> do
    e' <- lowerTerm e
    pure (LetProjectH p' x' proj' e')
lowerTerm (H.AllocClosure cs e) = do
  withClosures cs $ \es' cs' -> do
    e' <- lowerTerm e
    pure (AllocClosures es' cs' e')

lowerClosureArg :: H.ClosureArg -> M ClosureArg
lowerClosureArg (H.ValueArg x) = ValueArg <$> lowerName x
lowerClosureArg (H.TypeArg s) = TypeArg <$> lowerSort s

lowerProjection :: H.Projection -> M Projection
lowerProjection H.ProjectFst = pure ProjectFst
lowerProjection H.ProjectSnd = pure ProjectSnd
lowerProjection (H.ProjectField f) = ProjectField <$> lowerFieldLabel f

lowerValue :: H.ValueH -> M ValueH
lowerValue (H.IntH i) = pure (IntH i)
lowerValue (H.StringValH s) = pure (StringValH s)
lowerValue (H.CharValH c) = pure (CharValH c)
lowerValue (H.PairH x y) = PairH <$> lowerName x <*> lowerName y
lowerValue H.NilH = pure NilH
lowerValue H.WorldToken = pure WorldToken
lowerValue (H.RecordValH fields) = RecordH <$> traverse lowerField fields
  where lowerField (f, x) = (,) <$> lowerFieldLabel f <*> lowerName x
lowerValue (H.CtorAppH capp) = lowerCtorApp capp

-- Slightly messy, because booleans are ctorapp in Hoist, but back to being Value in Lower
lowerCtorApp :: H.CtorAppH -> M ValueH
lowerCtorApp (H.BoolH b) = pure (BoolH b)
lowerCtorApp (H.CtorApp c xs) =
  CtorAppH <$> (CtorApp <$> lowerCtor c <*> traverse lowerName xs)

lowerPrimOp :: H.PrimOp -> M PrimOp
lowerPrimOp (H.PrimAddInt64 x y) = PrimAddInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimSubInt64 x y) = PrimSubInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimMulInt64 x y) = PrimMulInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimNegInt64 x) = PrimNegInt64 <$> lowerName x
lowerPrimOp (H.PrimEqInt64 x y) = PrimEqInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimNeInt64 x y) = PrimNeInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimLtInt64 x y) = PrimLtInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimLeInt64 x y) = PrimLeInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimGeInt64 x y) = PrimGtInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimGtInt64 x y) = PrimGeInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimEqChar x y) = PrimEqChar <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimConcatenate x y) = PrimConcatenate <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimStrlen x) = PrimStrlen <$> lowerName x
lowerPrimOp (H.PrimIndexStr x y) = PrimIndexStr <$> lowerName x <*> lowerName y

lowerIOPrimOp :: H.PrimIO -> M PrimIO
lowerIOPrimOp (H.PrimGetLine x) = PrimGetLine <$> lowerName x
lowerIOPrimOp (H.PrimPutLine x y) = PrimPutLine <$> lowerName x <*> lowerName y

lowerCaseAlt :: (H.Ctor, H.Name) -> M CaseAlt
lowerCaseAlt (c, k) =
  CaseAlt <$> lowerCtor c <*> lookupThunkType k <*> lowerName k

lowerSort :: H.Sort -> M Sort
lowerSort (H.AllocH aa) = AllocH <$> lowerTyVar aa
lowerSort H.IntegerH = pure IntegerH
lowerSort H.BooleanH = pure BooleanH
lowerSort H.UnitH = pure UnitH
lowerSort H.StringH = pure StringH
lowerSort H.CharH = pure CharH
lowerSort (H.ProductH t s) = ProductH <$> lowerSort t <*> lowerSort s
lowerSort (H.ClosureH tele) = ClosureH <$> lowerClosureTele tele
lowerSort (H.RecordH fields) = TyRecordH <$> traverse lowerField fields
  where lowerField (f, t) = (,) <$> lowerFieldLabel f <*> lowerSort t
lowerSort (H.TyConH tc) = TyConH <$> lowerTyCon tc
lowerSort (H.TyAppH t s) = TyAppH <$> lowerSort t <*> lowerSort s
lowerSort H.TokenH = pure TokenH

lowerClosureTele :: H.ClosureTele -> M ClosureTele
lowerClosureTele (H.ClosureTele tele) = withTele tele $ \tele' -> pure (ClosureTele tele')

withTele :: [H.TeleEntry] -> ([TeleEntry] -> M a) -> M a
withTele [] k = k []
withTele (H.ValueTele s : tele) k = do
  s' <- lowerSort s
  withTele tele $ \tele' -> k (ValueTele s' : tele')
withTele (H.TypeTele aa kk : tele) k =
  withTyVar aa kk $ \aa' kk' ->
    withTele tele $ \tele' -> k (TypeTele aa' kk' : tele')

lowerKind :: H.Kind -> M Kind
lowerKind H.Star = pure Star
lowerKind (H.KArr k1 k2) = KArr <$> lowerKind k1 <*> lowerKind k2

-- Lower an occurrence of a name: either a local reference or an environment
-- reference.
lowerName :: H.Name -> M Name
lowerName x = do
  env <- asks envNames
  case Map.lookup x env of
    Nothing -> error "name not in scope"
    Just x' -> pure x'

-- Lower an occurrence of a type variable.
lowerTyVar :: H.TyVar -> M TyVar
lowerTyVar aa = do
  env <- asks envTyVars
  case Map.lookup aa env of
    Nothing -> error "tyvar not in scope"
    Just aa' -> pure aa'

lowerCtor :: H.Ctor -> M Ctor
lowerCtor c = do
  env <- asks envCtors
  case Map.lookup c env of
    Nothing -> error ("lowerCtor: ctor not in scope: " ++ show c)
    Just c' -> pure c'

lowerTyCon :: H.TyCon -> M TyCon
lowerTyCon tc = do
  env <- asks envTyCons
  case Map.lookup tc env of
    Nothing -> error "tycon not in scope"
    Just tc' -> pure tc'

newtype M a = M { getM :: Reader LowerEnv a }
deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader LowerEnv M

data LowerEnv
  = LowerEnv {
    envNames :: Map H.Name Name
  , envTyVars :: Map H.TyVar TyVar
  , envTyCons :: Map H.TyCon TyCon
  , envCtors :: Map H.Ctor Ctor
  , envThunkTypes :: Map H.Name ThunkType
  , envEnvTyCons :: Map H.CodeLabel TyCon
  }

runM :: M a -> a
runM = flip runReader emptyEnv . getM
  where
    emptyEnv = LowerEnv {
        envNames = Map.empty
      , envTyVars = Map.empty
      , envTyCons = Map.empty
      , envCtors = Map.empty
      , envThunkTypes = Map.empty
      , envEnvTyCons = Map.empty
      }

-- This isn't actually a scoping operation anymore, since I pass the env ptr
-- directly to withEnvFields, but it's still semi-useful to indicate that the
-- env ptr is "in scope".
withEnvPtr :: H.Id -> (Id -> M a) -> M a
withEnvPtr (H.Id envName) k = do
  let envName' = Id envName
  k envName'

-- Problem: this needs to be in scope for all subsequent closures, not just the
-- body of the current closure. Think about how to do this.
withCodeLabel :: H.CodeLabel -> (CodeLabel -> TyCon -> M a) -> M a
withCodeLabel l@(H.CodeLabel x) k = do
  let l' = CodeLabel x
  let envTyCon = TyCon (x ++ "_env")
  let extend env = env { envEnvTyCons = Map.insert l envTyCon (envEnvTyCons env) }
  local extend $ k l' envTyCon

withParams :: [H.ClosureParam] -> ([ClosureParam] -> M a) -> M a
withParams [] k = k []
withParams (H.PlaceParam p : ps) k =
  withPlace p $ \p' -> withParams ps (\ps' -> k (PlaceParam p':ps'))
withParams (H.TypeParam aa kk : ps) k =
  withTyVar aa kk $ \aa' kk' -> withParams ps (\ps' -> k (TypeParam aa' kk':ps'))

withClosures :: [H.ClosureAlloc] -> ([EnvAlloc] -> [ClosureAlloc] -> M a) -> M a
withClosures cs k = do
  withPlaces (map H.closurePlace cs) $ \ps' -> do
    (es', cs') <- unzip <$> traverse lowerClosureAlloc (zip ps' cs)
    k es' cs'

lowerClosureAlloc :: (Place, H.ClosureAlloc) -> M (EnvAlloc, ClosureAlloc)
lowerClosureAlloc (p', H.ClosureAlloc _p l envp (H.EnvAlloc tys xs)) = do
  l' <- lowerCodeLabel l
  tc <- lookupEnvTyCon l
  envp' <- lowerId envp
  tys' <- traverse lowerSort tys
  xs' <- traverse (\ (fld, x) -> (,) <$> lowerId fld <*> lowerName x) xs
  let enva = EnvAlloc envp' tc xs'
  let closa = ClosureAlloc p' l' tys' envp'
  pure (enva, closa)


withPlace :: H.Place -> (Place -> M a) -> M a
withPlace (H.Place s x) k = do
  s' <- lowerSort s
  x' <- lowerId x
  let p' = Place s' x'
  let (occ, occ') = (H.LocalName x, LocalName x')
  -- Places that have a closure type are associated with a Thunk Type: the
  -- calling convention used to invoke that closure.
  let
    extendThunk = case s' of
      ClosureH tele -> Map.insert occ (teleThunkType tele)
      _ -> id
  let
    extend env =
      env {
          envNames = Map.insert occ occ' (envNames env)
        , envThunkTypes = extendThunk (envThunkTypes env)
        }
  local extend $ k p'

withTyVar :: H.TyVar -> H.Kind -> (TyVar -> Kind -> M a) -> M a
withTyVar aa@(H.TyVar i) kk k = do
  aa' <- TyVar <$> lowerId i
  kk' <- lowerKind kk
  let extend env = env { envTyVars = Map.insert aa aa' (envTyVars env) }
  local extend $ k aa' kk'

-- Hmm. Something to think about:
-- This function implements lowering for a sequence of value bindings.
-- I also need lowering for a group of value bindings (closure allocation)
-- Likewise, ctor decls are basically unordered, and introduced as a group.
withPlaces :: [H.Place] -> ([Place] -> M a) -> M a
withPlaces [] k = k []
withPlaces (p:ps) k = withPlace p $ \p' ->
  withPlaces ps $ \ps' ->
    k (p':ps')

withTyVars :: [(H.TyVar, H.Kind)] -> ([(TyVar, Kind)] -> M a) -> M a
withTyVars [] k = k []
withTyVars ((aa, kk):tys) k =
  withTyVar aa kk $ \aa' kk' ->
    withTyVars tys $ \tys' ->
      k ((aa', kk'):tys')

withTyCon :: H.TyCon -> (TyCon -> M a) -> M a
withTyCon tc@(H.TyCon x) k = do
  let tc' = TyCon x
  let extend env = env { envTyCons = Map.insert tc tc' (envTyCons env) }
  local extend $ k tc'

withCtor :: TyCon -> Int -> H.Ctor -> (Ctor -> M a) -> M a
withCtor tc' i c@(H.Ctor x) k = do
  let c' = Ctor tc' (Id x) i
  let extend env = env { envCtors = Map.insert c c' (envCtors env) }
  local extend $ k c'

lookupThunkType :: H.Name -> M ThunkType
lookupThunkType x = do
  env <- asks envThunkTypes
  case Map.lookup x env of
    Nothing -> error "calling convention missing for variable"
    Just ty -> pure ty



-- | A thunk type is a calling convention for closures: the set of arguments
-- that must be provided to open it. This information is used to generate
-- trampolined tail calls.
--
-- Because 'ThunkType' is mostly concerned with the call site, it does not have
-- a binding structure. (Or does it?)
data ThunkType = ThunkType { thunkArgs :: [ThunkArg] }

data ThunkArg
  = ThunkValueArg Sort
  | ThunkTypeArg -- Arguably, I should include a kind here.

instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode

-- | Construct a thunk type from a closure telescope.
teleThunkType :: ClosureTele -> ThunkType
teleThunkType (ClosureTele ss) = ThunkType (map f ss)
  where
    f (ValueTele s) = ThunkValueArg s
    f (TypeTele aa k) = ThunkTypeArg

thunkTypeCode :: ThunkType -> String
thunkTypeCode (ThunkType ts) = concatMap argcode ts
  where
    argcode ThunkTypeArg = "I"
    argcode (ThunkValueArg s) = tycode s
    tycode :: Sort -> String
    tycode IntegerH = "V"
    tycode BooleanH = "B"
    tycode StringH = "T"
    tycode CharH = "H"
    tycode UnitH = "U"
    tycode TokenH = "K"
    -- In C, polymorphic types are represented uniformly.
    -- For example, 'list int64' and 'list (aa * bool)' are both represented
    -- using a 'struct list_val *' value. Therefore, when encoding a thunk type
    -- (that is, summarizing a closure's calling convention), we only need to
    -- mention the outermost constructor.
    tycode (ClosureH _) = "C"
    tycode (AllocH _) = "A"
    tycode (ProductH _ _) = "Q"
    tycode (TyRecordH _) = "R"
    tycode (TyConH tc) = let n = show tc in show (length n) ++ n
    tycode (TyAppH t _) = tycode t




-- | An 'Id' is any type of identifier.
newtype Id = Id String
  deriving (Eq, Ord)

instance Show Id where
  show (Id x) = x

-- | A 'Name' refers to a 'Place'. It is either a 'Place' in the local
-- scope, or in the environment scope.
--
-- An 'EnvName' contains the environment pointer that it dereferences
data Name = LocalName Id | EnvName Id Id
  deriving (Eq, Ord)

instance Show Name where
  show (LocalName x) = show x
  show (EnvName envp x) = show envp ++ "." ++ show x

-- | A 'Place' is a location that can hold a value. It has an identifier and a
-- sort that specifies what values can be stored there.
data Place = Place { placeSort :: Sort, placeName :: Id }

data TyVar = TyVar Id
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa) = show aa

-- | 'CodeLabel's are used to reference top-level code definitions. In
-- particular, a closure is constructed by pairing a code name with an
-- appropriate closure environment.
newtype CodeLabel = CodeLabel String
  deriving (Eq, Ord)

instance Show CodeLabel where
  show (CodeLabel d) = '#' : d


newtype TyCon = TyCon String
  deriving (Eq, Ord)

instance Show TyCon where
  show (TyCon tc) = tc

data Ctor = Ctor { ctorTyCon :: TyCon, ctorName :: Id, ctorDiscriminant :: Int }
  deriving (Eq, Ord)

instance Show Ctor where
  show (Ctor tc c _) = show tc ++ "::" ++ show c

newtype FieldLabel = FieldLabel String
  deriving (Eq)

instance Show FieldLabel where
  show (FieldLabel f) = f



data Program = Program [Decl] TermH

data Decl
  = DeclData DataDecl
  | DeclEnv EnvDecl
  | DeclCode CodeDecl


data EnvDecl
  = EnvDecl TyCon [(Id, Sort)]

data CodeDecl
  = CodeDecl CodeLabel [(TyVar, Kind)] (Id, TyCon) [ClosureParam] TermH

codeDeclName :: CodeDecl -> CodeLabel
codeDeclName (CodeDecl c _ _ _ _) = c 

codeDeclTele :: CodeDecl -> ClosureTele
codeDeclTele (CodeDecl _ _ _ params _) = ClosureTele (map f params)
  where
    f (PlaceParam p) = ValueTele (placeSort p)
    f (TypeParam aa k) = TypeTele aa k

data ClosureParam = PlaceParam Place | TypeParam TyVar Kind


data DataDecl
  = DataDecl TyCon [CtorDecl]

data CtorDecl
  -- Can't just use 'ClosureTele' here, because ctor applications actually return a value.
  -- (Also, I don't support existential ADTs yet, so I can't have TypeTele in here.)
  --
  -- Also, I don't have GADTs, so the return type is redundant (it's just the
  -- tycon applied to the parameters)
  --
  -- Third, I require each ctor argument to have a name (for fields in the ctor's struct),
  -- which doesn't fit in a 'ClosureTele' (but maybe 'ClosureParam' would work?
  -- Isomorphic, but semantically distinct, so not really.)
  = CtorDecl Ctor [(TyVar, Kind)] [(Id, Sort)]


-- | A 'Sort' describes the runtime layout of a value. It is static information.
data Sort
  = AllocH TyVar
  | IntegerH
  | BooleanH
  | UnitH
  | StringH
  | CharH
  | ProductH Sort Sort
  | ClosureH ClosureTele
  | TyRecordH [(FieldLabel, Sort)]
  | TyConH TyCon
  | TyAppH Sort Sort
  | TokenH

-- It's a bit unfortunate, but I do need to have separate telescopes for
-- parameters and types. The difference is that parameters need names for each
-- value, but closure types ignore value parameter names, and also cannot infer
-- those names.
newtype ClosureTele = ClosureTele [TeleEntry]

data TeleEntry
  = ValueTele Sort
  | TypeTele TyVar Kind

instance Eq Sort where
  (==) = equalSort emptyAE

data Kind = Star | KArr Kind Kind
  deriving (Eq)

asTyConApp :: Sort -> Maybe TyConApp
asTyConApp (TyConH tc) = Just (TyConApp tc [])
asTyConApp (TyAppH t s) = go t [s]
  where
    go (TyAppH t' s') acc = go t' (s' : acc)
    go (TyConH tc) acc = Just (TyConApp tc acc)
    -- Hmm. is 'f Int Bool Char' a TyConApp? I don't think so. You can't
    -- construct ctors or case on it.
    go _ _ = Nothing
asTyConApp _ = Nothing

fromTyConApp :: TyConApp -> Sort
fromTyConApp (TyConApp tc args) = foldl TyAppH (TyConH tc) args

data TyConApp = TyConApp TyCon [Sort]




data TermH
  -- 'let x : int = 17 in e'
  = LetValH Place ValueH TermH
  -- 'let z : bool = prim_int64gt(x, y) in e'
  | LetPrimH Place PrimOp TermH
  -- 'let s1 : token#, x : t <- prim_putLine(s0, msg) in e'
  | LetBindH Place Place PrimIO TermH
  -- 'let x : int64 = y .fst in e'
  | LetProjectH Place Name Projection TermH
  -- 'letrec (f1 : closure(ss) = #f1 { env1 })+ in e'
  -- Closures may be mutually recursive, so they are allocated as a group.
  | AllocClosures [EnvAlloc] [ClosureAlloc] TermH
  -- 'halt @bool x'
  | HaltH Sort Name
  -- 'call f (x, @int, z)', annotated with calling convention
  | OpenH ThunkType Name [ClosureArg]
  -- 'case x of { c1 -> k1 | c2 -> k2 | ... }'
  | CaseH Name TyConApp [CaseAlt]
  -- 'case x of { 17 -> k1 | 32 -> k2 | ... | default -> kd }'
  | IntCaseH Name [(Int64, ThunkType, Name)] -- all thunktypes should be no-arg, ThunkType []

data Projection = ProjectFst | ProjectSnd | ProjectField FieldLabel

data ClosureArg = ValueArg Name | TypeArg Sort

data CaseAlt = CaseAlt Ctor ThunkType Name

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: Place
  , closureDecl :: CodeLabel
  , closureCodeInst :: [Sort]
  , closureEnvRef :: Id
  }

data EnvAlloc
  = EnvAlloc Id TyCon [(Id, Name)]


data ValueH
  = IntH Int64
  | BoolH Bool
  | StringValH String
  | CharValH Char
  | PairH Name Name
  | NilH
  | WorldToken
  | RecordH [(FieldLabel, Name)]
  | CtorAppH CtorAppH

data CtorAppH
  = CtorApp Ctor [Name]

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
  | PrimEqChar Name Name
  | PrimConcatenate Name Name
  | PrimStrlen Name
  | PrimIndexStr Name Name

data PrimIO
  = PrimGetLine Name
  | PrimPutLine Name Name



-- Nameplate operations: FV, alpha-equality, and substitution

-- | An efficient computation for collecting free type variables.
-- The first parameter is a set of bound variables, that must be ignored.
-- The second parameter is an accumulator, much like a DList.
newtype FV = FV { runFV :: Set TyVar -> Set TyVar -> Set TyVar }

unitFV :: TyVar -> FV
unitFV aa = FV $ \bound acc ->
  if Set.notMember aa bound && Set.notMember aa acc then
    Set.insert aa acc
  else
    acc

bindFV :: TyVar -> FV -> FV
bindFV aa f = FV $ \bound acc -> runFV f (Set.insert aa bound) acc

instance Semigroup FV where
  f <> g = FV $ \bound acc -> runFV f bound (runFV g bound acc)

instance Monoid FV where
  mempty = FV $ \_ acc -> acc

freeTyVars :: Sort -> Set TyVar
freeTyVars s = runFV (ftv s) Set.empty Set.empty

ftv :: Sort -> FV
ftv (AllocH aa) = unitFV aa
ftv (TyConH _) = mempty
ftv UnitH = mempty
ftv IntegerH = mempty
ftv BooleanH = mempty
ftv StringH = mempty
ftv CharH = mempty
ftv TokenH = mempty
ftv (ProductH t s) = ftv t <> ftv s
ftv (TyRecordH fs) = foldMap (ftv . snd) fs
ftv (TyAppH t s) = ftv t <> ftv s
ftv (ClosureH tele) = ftvTele tele

ftvTele :: ClosureTele -> FV
ftvTele (ClosureTele tele) = go tele
  where
    go [] = mempty
    go (ValueTele s : rest) = ftv s <> go rest
    go (TypeTele aa _ : rest) = bindFV aa (go rest)

-- | An environment used when checking alpha-equality.
-- Contains the deBruijn level and a mapping from bound variables to levels for
-- both the LHS and RHS.
data AE = AE Int (Map TyVar Int) (Map TyVar Int)

-- | The initial alpha-equality environment.
emptyAE :: AE
emptyAE = AE 0 Map.empty Map.empty

lookupAE :: AE -> TyVar -> TyVar -> Bool
lookupAE (AE _ lhs rhs) aa bb =  case (Map.lookup aa lhs, Map.lookup bb rhs) of
  (Just la, Just lb) -> la == lb
  (Nothing, Nothing) -> aa == bb
  (_, _) -> False

bindAE :: TyVar -> TyVar -> AE -> AE
bindAE aa bb (AE l lhs rhs) = AE (l+1) (Map.insert aa l lhs) (Map.insert bb l rhs)

-- | Test alpha-equality of two sorts.
equalSort :: AE -> Sort -> Sort -> Bool
equalSort ae (AllocH aa) (AllocH bb) = lookupAE ae aa bb
equalSort _ (AllocH _) _ = False
equalSort _e (TyConH tc1) (TyConH tc2) = tc1 == tc2
equalSort _ (TyConH _) _ = False
equalSort _ IntegerH IntegerH = True
equalSort _ IntegerH _ = False
equalSort _ BooleanH BooleanH = True
equalSort _ BooleanH _ = False
equalSort _ UnitH UnitH = True
equalSort _ UnitH _ = False
equalSort _ StringH StringH = True
equalSort _ StringH _ = False
equalSort _ CharH CharH = True
equalSort _ CharH _ = False
equalSort _ TokenH TokenH = True
equalSort _ TokenH _ = False
equalSort ae (ProductH s1 s2) (ProductH t1 t2) = equalSort ae s1 t1 && equalSort ae s2 t2
equalSort _ (ProductH _ _) _ = False
equalSort ae (TyRecordH fs1) (TyRecordH fs2) = go fs1 fs2
  where
    go [] [] = True
    go ((f1, t1):fs1') ((f2, t2):fs2') = f1 == f2 && equalSort ae t1 t2 && go fs1' fs2'
    go _ _ = False
equalSort _ (TyRecordH _) _ = False
equalSort ae (TyAppH s1 s2) (TyAppH t1 t2) = equalSort ae s1 t1 && equalSort ae s2 t2
equalSort _ (TyAppH _ _) _ = False
equalSort ae (ClosureH ss) (ClosureH ts) = equalTele ae ss ts
equalSort _ (ClosureH _) _ = False

equalTele :: AE -> ClosureTele -> ClosureTele -> Bool
equalTele ae0 (ClosureTele tele) (ClosureTele tele') = go ae0 tele tele'
  where
    go _ [] [] = True
    go ae (ValueTele s : ls) (ValueTele t : rs) = equalSort ae s t && go ae ls rs
    go _ (ValueTele _ : _) (_ : _) = False
    go ae (TypeTele aa k1 : ls) (TypeTele bb k2 : rs) =
      k1 == k2 && go (bindAE aa bb ae) ls rs
    go _ (TypeTele _ _ : _) (_ : _) = False
    go _ (_ : _) [] = False
    go _ [] (_ : _) = False


-- | A substitution maps free type variables to sorts, avoiding free variable
-- capture when it passes under type variable binders.
data Subst = Subst { substScope :: Set TyVar, substMapping :: Map TyVar Sort }

-- | Construct a singleton substitution, @[aa := s]@.
singleSubst :: TyVar -> Sort -> Subst
singleSubst aa s =
  -- We must not capture any free variable of 's', so the scope is intially set
  -- to 'FTV(s)'.
  Subst { substScope = freeTyVars s, substMapping = Map.singleton aa s }

listSubst :: [(TyVar, Sort)] -> Subst
listSubst xs = Subst { substScope = foldMap (freeTyVars . snd) xs, substMapping = Map.fromList xs }

-- | Pass a substitution under a variable binder, returning the updated
-- substitution, and a new variable binder.
substBind :: Subst -> TyVar -> (Subst, TyVar)
substBind (Subst sc sub) aa =
  if Set.notMember aa sc then
    (Subst (Set.insert aa sc) (Map.delete aa sub), aa)
  else
    go (0 :: Int)
  where
    go i =
      let TyVar (Id aa') = aa in
      let bb = TyVar (Id (aa' ++ show i)) in
      if Set.notMember bb sc then
        (Subst (Set.insert bb sc) (Map.insert aa (AllocH bb) sub), bb)
      else
        go (i+1)

lookupSubst :: TyVar -> Subst -> Maybe Sort
lookupSubst aa (Subst _ sub) = Map.lookup aa sub

-- | Apply a substitution to a sort.
substSort :: Subst -> Sort -> Sort
substSort sub (AllocH aa) = case lookupSubst aa sub of
  Nothing -> AllocH aa
  Just s -> s
substSort _ (TyConH tc) = TyConH tc
substSort _ IntegerH = IntegerH
substSort _ BooleanH = BooleanH
substSort _ UnitH = UnitH
substSort _ StringH = StringH
substSort _ CharH = CharH
substSort _ TokenH = TokenH
substSort sub (ProductH s t) = ProductH (substSort sub s) (substSort sub t)
substSort sub (TyRecordH fs) = TyRecordH (map (second (substSort sub)) fs)
substSort sub (TyAppH s t) = TyAppH (substSort sub s) (substSort sub t)
substSort sub (ClosureH tele) = ClosureH (substTele sub tele)

substTele :: Subst -> ClosureTele -> ClosureTele
substTele subst (ClosureTele tele) = ClosureTele (go subst tele)
  where
    go _ [] = []
    go sub (ValueTele s : tele') = ValueTele (substSort sub s) : go sub tele'
    go sub (TypeTele aa k : tele') = case substBind sub aa of
      (sub', aa') -> TypeTele aa' k : go sub' tele'


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintProgram :: Program -> String
pprintProgram (Program ds srcH) = pprintDecls ds ++ ";;\n" ++ pprintTerm 0 srcH

pprintDecls :: [Decl] -> String
pprintDecls ds = concatMap pprintDecl ds
  where
    pprintDecl (DeclEnv ed) = pprintEnvDecl 0 ed
    pprintDecl (DeclCode cd) = pprintClosureDecl 0 cd
    pprintDecl (DeclData dd) = pprintDataDecl 0 dd

pprintEnvDecl :: Int -> EnvDecl -> String
pprintEnvDecl n (EnvDecl l fields) =
  indent n ("environment " ++ show l ++ "::Env = {" ++ intercalate ", " (map pprintEnvField fields) ++ "}\n")
  where pprintEnvField (x, s) = show x ++ " : " ++ pprintSort s

pprintClosureDecl :: Int -> CodeDecl -> String
pprintClosureDecl n (CodeDecl f aas (envName, envTyCon) params e) =
  indent n ("code " ++ show f ++ "[" ++ tyParams ++ "](" ++ envParam ++ ", " ++ valueParams ++ ") =\n") ++
  pprintTerm (n+2) e
  where
    tyParams = intercalate ", " typeFields
    typeFields = map (\ (aa, k) -> "@" ++ show aa ++ " : " ++ pprintKind k) aas
    envParam = show envName ++ " : " ++ show envTyCon
    valueParams = intercalate ", " (map pprintParam params)

pprintDataDecl :: Int -> DataDecl -> String
pprintDataDecl n (DataDecl tc ctors) =
  indent n ("data " ++ show tc ++ " where\n") ++
  unlines (map (pprintCtorDecl (n+2)) ctors)

pprintCtorDecl :: Int -> CtorDecl -> String
pprintCtorDecl n (CtorDecl c tys args) =
  indent n (show c ++ "[" ++ intercalate ", " (map g tys) ++ "](" ++ intercalate ", " (map f args) ++ ");")
  where
    f (x, s) = show x ++ " : " ++ pprintSort s
    g (aa, k) = "@" ++ show aa ++ " : " ++ pprintKind k

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH s x) = indent n $ "HALT @" ++ pprintSort s ++ " " ++ show x ++ ";\n"
pprintTerm n (OpenH _ty c args) =
  indent n $ intercalate " " (show c : map pprintClosureArg args) ++ ";\n"
pprintTerm n (CaseH x _kind ks) =
  let branches = intercalate " | " (map (\ (CaseAlt c _ty k) -> show c ++ " -> " ++ show k) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (IntCaseH x ks) =
  let branches = intercalate " | " (map (\ (i, _, k) -> show i ++ " -> " ++ show k) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetValH x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetProjectH x y p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ proj p ++ " " ++ show y ++ ";\n") ++ pprintTerm n e
  where
    proj ProjectFst = "fst"
    proj ProjectSnd = "snd"
    proj (ProjectField f) = show f
pprintTerm n (LetPrimH x p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintPrim p ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetBindH p1 p2 prim e) =
  indent n ("let " ++ ps ++ " = " ++ pprintPrimIO prim ++ ";\n") ++ pprintTerm n e
  where ps = pprintPlace p1 ++ ", " ++ pprintPlace p2
pprintTerm n (AllocClosures es cs e) =
  indent n "let\n" ++ concatMap (pprintEnvAlloc (n+2)) es ++ concatMap (pprintClosureAlloc (n+2)) cs ++ indent n "in\n" ++ pprintTerm n e

pprintClosureArg :: ClosureArg -> String
pprintClosureArg (TypeArg s) = '@' : pprintSort s
pprintClosureArg (ValueArg x) = show x

pprintValue :: ValueH -> String
pprintValue (PairH x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue NilH = "()"
pprintValue (IntH i) = show i
pprintValue (BoolH b) = if b then "true" else "false"
pprintValue (StringValH s) = show s
pprintValue (CharValH c) = show c
pprintValue WorldToken = "WORLD#"
pprintValue (RecordH []) = "{}"
pprintValue (RecordH xs) = "{ " ++ intercalate ", " (map pprintField xs) ++ " }"
  where pprintField (f, x) = show f ++ " = " ++ show x
pprintValue (CtorAppH capp) = pprintCtorApp capp

pprintCtorApp :: CtorAppH -> String
pprintCtorApp (CtorApp c xs) =
  show c ++ "(" ++ intercalate ", " (map show xs) ++ ")"

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
pprintPrim (PrimEqChar x y) = "prim_eqchar(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimConcatenate x y) = "prim_concatenate(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimStrlen x) = "prim_strlen(" ++ show x ++ ")"
pprintPrim (PrimIndexStr x y) = "prim_strindex(" ++ show x ++ ", " ++ show y ++ ")"

pprintPrimIO :: PrimIO -> String
pprintPrimIO (PrimGetLine x) = "prim_getLine(" ++ show x ++ ")"
pprintPrimIO (PrimPutLine x y) = "prim_putLine(" ++ show x ++ ", " ++ show y ++ ")"

pprintPlace :: Place -> String
pprintPlace (Place s x) = show x ++ " : " ++ pprintSort s

pprintParam :: ClosureParam -> String
pprintParam (PlaceParam p) = pprintPlace p
pprintParam (TypeParam aa k) = '@' : show aa ++ " : " ++ pprintKind k

pprintEnvAlloc :: Int -> EnvAlloc -> String
pprintEnvAlloc n (EnvAlloc p tc fs) =
  indent n $ show p ++ " : " ++ show tc ++ " = {" ++ intercalate ", " (map pprintAllocArg fs) ++ "}\n"

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d tys env) =
  indent n $ pprintPlace p ++ " = <<" ++ show d ++ " " ++ intercalate " @" (map pprintSort tys) ++ ", " ++ show env ++ ">>\n"

pprintAllocArg :: (Id, Name) -> String
pprintAllocArg (field, x) = show field ++ " = " ++ show x

pprintSort :: Sort -> String
pprintSort IntegerH = "int"
pprintSort BooleanH = "bool"
pprintSort UnitH = "unit"
pprintSort StringH = "string"
pprintSort CharH = "char"
pprintSort TokenH = "token#"
pprintSort (ProductH t s) = "pair " ++ pprintSort t ++ " " ++ pprintSort s
pprintSort (TyRecordH []) = "{}"
pprintSort (TyRecordH fs) = "{ " ++ intercalate ", " (map pprintField fs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintSort t
pprintSort (TyAppH t s) = pprintSort t ++ " " ++ pprintSort s
pprintSort (ClosureH tele) = "closure(" ++ pprintTele tele ++ ")"
pprintSort (AllocH aa) = show aa
pprintSort (TyConH tc) = show tc

pprintTele :: ClosureTele -> String
pprintTele (ClosureTele ss) = intercalate ", " (map f ss)
  where
    f (ValueTele s) = pprintSort s
    f (TypeTele aa k) = "forall " ++ show aa ++ " : " ++ pprintKind k

pprintKind :: Kind -> String
pprintKind Star = "*"
pprintKind (KArr Star k2) = "* -> " ++ pprintKind k2
pprintKind (KArr k1 k2) = "(" ++ pprintKind k1 ++ ") -> " ++ pprintKind k2
