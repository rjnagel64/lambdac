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
    , ThunkType(..)
    , PlaceName(..)
    , FieldName(..)
    , InfoName(..)
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
import Control.Monad.Writer hiding (Sum)
import Control.Monad.State

import Data.Bifunctor
import Data.Int (Int64)
import Data.Traversable (for, mapAccumL)
import Data.List (intercalate, nub)

import qualified CC as C
import CC (TermC(..), ValueC(..), ArithC(..), CmpC(..), Sort(..), ThunkType(..))

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
data PlaceName = PlaceName { placeSort :: Sort, placeName :: String }

data FieldName = FieldName { fieldSort :: Sort, fieldName :: String }

asPlaceName :: Sort -> C.Name -> PlaceName
asPlaceName s (C.Name x i) = PlaceName s (x ++ show i)

asFieldName :: Sort -> C.Name -> FieldName
asFieldName s (C.Name x i) = FieldName s (x ++ show i)

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


-- TODO: I think that by 'Hoist', type parameters and value parameters should
-- be treated uniformly. E.G., 'ClosureDecl' should carry a '[ClosureParam]',
-- where 'data ClosureParam = ValueParam PlaceName | TypeParam InfoName'
data ClosureDecl
  = ClosureDecl DeclName (String, EnvDecl) [PlaceName] TermH

data EnvDecl = EnvDecl [InfoName] [FieldName]

data TermH
  = LetValH PlaceName ValueH TermH
  | LetPrimH PlaceName PrimOp TermH
  -- 'let value x = fst y in e'
  | LetProjectH PlaceName Name Projection TermH
  | HaltH Name Sort
  | OpenH Name ThunkType [Name] -- Open a closure, by providing a list of arguments.
  | CaseH Name CaseKind [(Name, ThunkType)]
  | InstH Name ThunkType [Sort] [Name]
  -- Closures may be mutually recursive, so are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

-- TODO(eventually): bring back generic case expressions
data CaseKind = CaseBool | CaseSum | CaseList

data Projection = ProjectFst | ProjectSnd

caseKind :: Sort -> CaseKind
caseKind Boolean = CaseBool
caseKind Sum = CaseSum
caseKind (List _) = CaseList
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
    envAllocInfoArgs :: [(InfoName, C.TyVar)]
  , envAllocFreeArgs :: [(FieldName, Name)]
  , envAllocRecArgs :: [(FieldName, Name)]
  }

data ValueH
  = IntH Int64
  | BoolH Bool
  | PairH (Name, Sort) (Name, Sort)
  | NilH
  | InlH Sort Name
  | InrH Sort Name
  | ListNilH
  | ConsH Sort Name Name

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

-- Note: FieldName:s should not be nested? after closure conversion, all names
-- in a definition are either parameters, local temporaries, or environment
-- field references.
data HoistEnv = HoistEnv (Map C.Name PlaceName) (Map C.Name FieldName)


newtype ClosureDecls = ClosureDecls [ClosureDecl]

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls

-- TODO: ThunkType2 should use deBruijn levels to refer to type variables
data ThunkType2 = ThunkType2 { thunkArgSorts :: [Sort] }

eqThunkType :: ThunkType2 -> ThunkType2 -> Bool
eqThunkType (ThunkType2 ts') (ThunkType2 ss') = go Map.empty Map.empty ts' ss'
  where
    go _ _ [] [] = True
    go fw bw (Alloc aa:ts) (Alloc bb:ss) = case (Map.lookup aa fw, Map.lookup bb bw) of
      (Nothing, Nothing) ->
        go (Map.insert aa bb fw) (Map.insert bb aa bw) ts ss
      (Just aa', Just bb') ->
        (aa' == bb && bb' == aa) && go (Map.insert aa bb fw) (Map.insert bb aa bw) ts ss
      (_, _) -> False
    go fw bw (t:ts) (s:ss) = eqSort t s && go fw bw ts ss
    go _ _ _ _ = False

    -- Test that two 'Sort's have the same runtime representation
    -- Basically, whether they have the same 'tycode'.
    eqSort (Alloc _) (Alloc _) = True
    eqSort (List t) (List s) = eqSort t s
    eqSort (Pair t1 t2) (Pair s1 s2) = eqSort t1 s1 && eqSort t2 s2
    eqSort (Closure xs) (Closure ys) = go2 xs ys
      where
        go2 [] [] = True
        go2 (t:ts) (s:ss) = eqSort t s && go2 ts ss
        go2 _ _ = False
    eqSort Integer Integer = True
    eqSort Unit Unit = True
    eqSort Boolean Boolean = True
    eqSort Sum Sum = True
    eqSort _ _ = False

instance Eq ThunkType2 where (==) = eqThunkType

-- | A set data type, that only requires 'Eq' constraints. Implemented because
-- I can't wrap my head around a sensible ordering for 'ThunkType' or
-- 'ThunkType2'.
newtype NubList a = NubList { getNubList :: [a] }

nubList :: Eq a => [a] -> NubList a
nubList xs = NubList (nub xs)

instance Eq a => Semigroup (NubList a) where
  NubList as <> NubList bs = NubList (merge as)
    where
      merge [] = bs
      merge (x:xs) = if elem x bs then merge xs else x : merge xs

instance Eq a => Monoid (NubList a) where
  mempty = NubList []

-- TODO: Collect thunk types here
-- (Hopefully, this will allow me to fix the issues with polymorphic thunk types)
newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set DeclName) (Writer (ClosureDecls, NubList ThunkType2))) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter (ClosureDecls, NubList ThunkType2) HoistM
deriving newtype instance MonadState (Set DeclName) HoistM

runHoist :: HoistM a -> (a, (ClosureDecls, [ThunkType2]))
runHoist = second (second getNubList) . runWriter .  flip evalStateT Set.empty .  flip runReaderT emptyEnv .  runHoistM
  where emptyEnv = HoistEnv mempty mempty

tellClosures :: [ClosureDecl] -> HoistM ()
tellClosures cs = tell (ClosureDecls cs, ts)
  where
    ts = nubList [ThunkType2 [placeSort p | p <- places] | ClosureDecl _ _ places _ <- cs]


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
hoist :: TermC -> HoistM TermH
hoist (HaltC x) = uncurry HaltH <$> hoistVarOcc' x
hoist (JumpC k xs) = do
  (ys, ss) <- unzip <$> traverse hoistVarOcc' xs
  OpenH <$> hoistVarOcc k <*> pure (ThunkType ss) <*> pure ys
hoist (CallC f xs ks) = do
  (ys, ss) <- unzip <$> traverse hoistVarOcc' (xs ++ ks)
  OpenH <$> hoistVarOcc f <*> pure (ThunkType ss) <*> pure ys
hoist (CaseC x t ks) = do
  x' <- hoistVarOcc x
  let kind = caseKind t
  ks' <- for ks $ \ (k, s) -> do
    k' <- hoistVarOcc k
    pure (k', s)
  pure $ CaseH x' kind ks'
hoist (InstC f ts ks) = do
  (ys, ss) <- unzip <$> traverse hoistVarOcc' ks
  InstH <$> hoistVarOcc f <*> pure (ThunkType ss) <*> pure ts <*> pure ys
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
      let ty = ThunkType ([s | (_x, s) <- xs] ++ [s | (_k, s) <- ks])
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
      let ty = ThunkType [s | (_x, s) <- xs]
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
      let ty = ThunkType [s | (_k, s) <- ks] -- Incorrect, needs type arguments.
      pure (ClosureAlloc p ty d env')
    e' <- hoist e
    pure (AllocClosure fs' e')

hoistEnvDef :: C.EnvDef -> HoistM EnvAlloc
hoistEnvDef (C.EnvDef tys free rec) =
  let tys' = map (\aa -> (asInfoName aa, aa)) tys in
  EnvAlloc tys' <$> traverse envAllocField free <*> traverse envAllocField rec

envAllocField :: (C.Name, Sort) -> HoistM (FieldName, Name)
envAllocField (x, s) = do
  let field = asFieldName s x
  x' <- hoistVarOcc x
  pure (field, x')


placesForClosureAllocs :: (a -> C.Name) -> (a -> Sort) -> [(DeclName, a)] -> ([(PlaceName, DeclName, a)] -> HoistM r) -> HoistM r
placesForClosureAllocs closureName closureSort cdecls kont = do
  HoistEnv scope _ <- ask
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
hoistValue (IntC i) = pure (IntH (fromIntegral i))
hoistValue (BoolC b) = pure (BoolH b)
hoistValue (PairC x y) = PairH <$> hoistVarOcc' x <*> hoistVarOcc' y
hoistValue NilC = pure NilH
hoistValue (InlC x) = uncurry (flip InlH) <$> hoistVarOcc' x
hoistValue (InrC x) = uncurry (flip InrH) <$> hoistVarOcc' x
hoistValue EmptyC = pure ListNilH
hoistValue (ConsC x xs) = uncurry (flip ConsH) <$> hoistVarOcc' x <*> hoistVarOcc xs

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


-- TODO: Pick name for environment parameter here.
hoistFunClosure :: (DeclName, C.FunClosureDef) -> HoistM ClosureDecl
hoistFunClosure (fdecl, C.FunClosureDef _f env xs ks body) = do
  (env', places', body') <- inClosure env (xs ++ ks) $ hoist body
  let fd = ClosureDecl fdecl env' places' body'
  pure fd

hoistContClosure :: (DeclName, C.ContClosureDef) -> HoistM ClosureDecl
hoistContClosure (kdecl, C.ContClosureDef _k env xs body) = do
  (env', places', body') <- inClosure env xs $ hoist body
  let kd = ClosureDecl kdecl env' places' body'
  pure kd

hoistAbsClosure :: (DeclName, C.AbsClosureDef) -> HoistM ClosureDecl
hoistAbsClosure (fdecl, C.AbsClosureDef _f env as ks body) = do
  -- TODO: Shouldn't hoistAbsClosure create parameters for the sorts?
  (env', places', body') <- inClosure env ks $ hoist body
  let fd = ClosureDecl fdecl env' places' body'
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
inClosure :: C.EnvDef -> [(C.Name, Sort)] -> HoistM a -> HoistM ((String, EnvDecl), [PlaceName], a)
inClosure (C.EnvDef tys free rec) places m = do
  -- Because this is a new top-level context, we do not have to worry about shadowing anything.
  let fields = free ++ rec
  let fields' = map (\ (x, s) -> (x, asFieldName s x)) fields
  let places' = map (\ (x, s) -> (x, asPlaceName s x)) places
  let tys' = map asInfoName tys
  let replaceEnv (HoistEnv _ _) = HoistEnv (Map.fromList places') (Map.fromList fields')
  r <- local replaceEnv m
  let inScopeNames = map (fieldName . snd) fields' ++ map (placeName . snd) places' ++ map infoName tys'
  let name = pickEnvironmentName (Set.fromList inScopeNames)
  pure ((name, EnvDecl tys' (map snd fields')), map snd places', r)

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

-- | Hoist a variable occurrence, and also retrieve its sort.
hoistVarOcc' :: C.Name -> HoistM (Name, Sort)
hoistVarOcc' x = do
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
pprintTerm n (HaltH x _) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (OpenH c _ xs) = indent n $ show c ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CaseH x _kind ks) =
  let branches = intercalate " | " (map (show . fst) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (InstH f _ty ss ks) =
  indent n $ intercalate " @" (show f : map show ss) ++ " " ++ intercalate " " (map show ks) ++ ";\n"
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

pprintValue :: ValueH -> String
pprintValue (PairH (x, _) (y, _)) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue NilH = "()"
pprintValue (IntH i) = show i
pprintValue (BoolH b) = if b then "true" else "false"
pprintValue (InlH _ x) = "inl " ++ show x
pprintValue (InrH _ y) = "inr " ++ show y
pprintValue ListNilH = "nil"
pprintValue (ConsH _ x xs) = "cons " ++ show x ++ " " ++ show xs

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
pprintPlace (PlaceName s x) = show s ++ " " ++ x

pprintField :: FieldName -> String
pprintField (FieldName s x) = show s ++ " " ++ x

pprintInfo :: InfoName -> String
pprintInfo (InfoName aa) = aa

pprintClosures :: [ClosureDecl] -> String
pprintClosures cs = "let {\n" ++ concatMap (pprintClosureDecl 2) cs ++ "}\n"

pprintClosureDecl :: Int -> ClosureDecl -> String
pprintClosureDecl n (ClosureDecl f (name, EnvDecl is fs) params e) =
  indent n (show f ++ " " ++ env ++ " (" ++ intercalate ", " (map pprintPlace params) ++ ") =\n") ++
  pprintTerm (n+2) e
  where env = name ++ " : {" ++ intercalate ", " (map pprintInfo is) ++ "; " ++ intercalate ", " (map pprintField fs) ++ "}"

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p _t d (EnvAlloc _info free rec)) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ env'
  where env' = "{" ++ intercalate ", " (map pprintAllocArg (free ++ rec)) ++ "}\n"

pprintAllocArg :: (FieldName, Name) -> String
pprintAllocArg (field, x) = pprintField field ++ " = " ++ show x
