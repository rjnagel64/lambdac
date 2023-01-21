
-- | A module describing the structure and syntactic operations on the Hoist IR.
module Hoist.IR
    ( Id(..)
    , Name(..)
    , Place(..)
    , TyVar(..)
    , CodeLabel(..)

    , Sort(..)
    , ClosureTele(..)
    , TeleEntry(..)
    , TyConApp(..)
    , asTyConApp

    , Kind(..)

    , Subst
    , singleSubst
    , listSubst
    , lookupSubst
    , substSort
    , substTele

    , CodeDecl(..)
    , codeDeclName
    , codeDeclTele
    , EnvDecl(..)
    , ClosureParam(..)

    , DataDecl(..)
    , TyCon(..)
    , CtorDecl(..)
    , Ctor(..)

    , TermH(..)
    , Projection(..)
    , ClosureArg(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , ValueH(..)
    , CtorAppH(..)
    , PrimOp(..)


    , Program(..)
    , Decl(..)
    , pprintProgram
    , pprintSort
    , pprintKind
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Int (Int64)
import Data.List (intercalate)


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

newtype Ctor = Ctor String
  deriving (Eq, Ord)

instance Show Ctor where
  show (Ctor c) = c



data Program = Program [Decl] TermH

data Decl
  = DeclCode CodeDecl
  | DeclData DataDecl


data CodeDecl
  = CodeDecl CodeLabel (Id, EnvDecl) [ClosureParam] TermH

codeDeclName :: CodeDecl -> CodeLabel
codeDeclName (CodeDecl c _ _ _) = c 

codeDeclTele :: CodeDecl -> ClosureTele
codeDeclTele (CodeDecl _ _ params _) = ClosureTele (map f params)
  where
    f (PlaceParam p) = ValueTele (placeSort p)
    f (TypeParam aa k) = TypeTele aa k

-- Hmm. EnvDecl does not need field names for the captured (singleton) types.
data EnvDecl = EnvDecl [(TyVar, Kind)] [Place]

data ClosureParam = PlaceParam Place | TypeParam TyVar Kind


data DataDecl
  = DataDecl TyCon [(TyVar, Kind)] [CtorDecl]

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
  = CtorDecl Ctor [(Id, Sort)]


-- | A 'Sort' describes the runtime layout of a value. It is static information.
data Sort
  = AllocH TyVar
  | IntegerH
  | BooleanH
  | UnitH
  | StringH
  | ProductH Sort Sort
  | SumH Sort Sort
  | ListH Sort
  | ClosureH ClosureTele
  | TyConH TyCon
  | TyAppH Sort Sort

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
asTyConApp BooleanH = Just CaseBool
asTyConApp (SumH t s) = Just (CaseSum t s)
asTyConApp (ListH t) = Just (CaseList t)
asTyConApp (TyConH tc) = Just (TyConApp tc [])
asTyConApp (TyAppH t s) = go t [s]
  where
    go (TyAppH t' s') acc = go t' (s' : acc)
    go (TyConH tc) acc = Just (TyConApp tc acc)
    -- Hmm. is 'f Int Bool Char' a TyConApp? I don't think so. You can't
    -- construct ctors or case on it.
    go _ _ = Nothing
asTyConApp _ = Nothing

data TyConApp = CaseBool | CaseSum Sort Sort | CaseList Sort | TyConApp TyCon [Sort]




data TermH
  -- 'let x : int = 17 in e'
  = LetValH Place ValueH TermH
  -- 'let z : bool = prim_int64gt(x, y) in e'
  | LetPrimH Place PrimOp TermH
  -- 'let x : int64 = y .fst in e'
  | LetProjectH Place Name Projection TermH
  -- 'halt @bool x'
  | HaltH Sort Name
  -- 'call f (x, @int, z, $string_info)'
  | OpenH Name [ClosureArg]
  -- 'case x of { c1 -> k1 | c2 -> k2 | ... }'
  | CaseH Name TyConApp [(Ctor, Name)]
  -- 'letrec (f1 : closure(ss) = #f1 { env1 })+ in e'
  -- Closures may be mutually recursive, so they are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

data Projection = ProjectFst | ProjectSnd

data ClosureArg = ValueArg Name | TypeArg Sort

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: Place
  , closureDecl :: CodeLabel
  , closureEnvPlace :: Id
  , closureEnv :: EnvAlloc
  }

-- Because a closure environment is basically an abstract record
-- '∃aa+.{ (l : s)+ }',
-- constructing a closure environment involves providing a sequence of type and
-- values for each field.
data EnvAlloc
  = EnvAlloc {
    envAllocTypeArgs :: [Sort]
  , envAllocValueArgs :: [(Id, Name)]
  }

data ValueH
  = IntH Int64
  | StringValH String
  | PairH Name Name
  | NilH
  | CtorAppH CtorAppH

data CtorAppH
  = BoolH Bool
  | InlH Name
  | InrH Name
  | ListNilH
  | ListConsH Name Name
  | CtorApp Ctor [Name]

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
  | PrimConcatenate Name Name
  | PrimStrlen Name



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
ftv (ListH t) = ftv t
ftv (ProductH t s) = ftv t <> ftv s
ftv (SumH t s) = ftv t <> ftv s
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
equalSort ae (ProductH s1 s2) (ProductH t1 t2) = equalSort ae s1 t1 && equalSort ae s2 t2
equalSort _ (ProductH _ _) _ = False
equalSort ae (SumH s1 s2) (SumH t1 t2) = equalSort ae s1 t1 && equalSort ae s2 t2
equalSort _ (SumH _ _) _ = False
equalSort ae (TyAppH s1 s2) (TyAppH t1 t2) = equalSort ae s1 t1 && equalSort ae s2 t2
equalSort _ (TyAppH _ _) _ = False
equalSort ae (ListH s) (ListH t) = equalSort ae s t
equalSort _ (ListH _) _ = False
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
substSort sub (ProductH s t) = ProductH (substSort sub s) (substSort sub t)
substSort sub (SumH s t) = SumH (substSort sub s) (substSort sub t)
substSort sub (TyAppH s t) = TyAppH (substSort sub s) (substSort sub t)
substSort sub (ListH t) = ListH (substSort sub t)
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
    pprintDecl (DeclCode cd) = pprintClosureDecl 0 cd
    pprintDecl (DeclData dd) = pprintDataDecl 0 dd

pprintClosureDecl :: Int -> CodeDecl -> String
pprintClosureDecl n (CodeDecl f (name, EnvDecl is fs) params e) =
  indent n ("code " ++ show f ++ " (" ++ envParam ++ "; " ++ intercalate ", " (map pprintParam params) ++ ") =\n") ++
  pprintTerm (n+2) e
  where
    envParam = show name ++ " : {" ++ intercalate ", " (typeFields ++ valueFields) ++ "}"
    typeFields = map (\ (aa, k) -> "@" ++ show aa ++ " : " ++ pprintKind k) is
    valueFields = map pprintPlace fs

pprintDataDecl :: Int -> DataDecl -> String
pprintDataDecl n (DataDecl tc params ctors) =
  indent n ("data " ++ show tc ++ intercalate " " (map f params) ++ " where\n") ++
  unlines (map (pprintCtorDecl (n+2)) ctors)
  where f (aa, k) = "(" ++ show aa ++ " : " ++ pprintKind k ++ ")"

pprintCtorDecl :: Int -> CtorDecl -> String
pprintCtorDecl n (CtorDecl c args) =
  indent n (show c ++ "(" ++ intercalate ", " (map f args) ++ ");")
  where f (x, s) = show x ++ " : " ++ pprintSort s

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH s x) = indent n $ "HALT @" ++ pprintSort s ++ " " ++ show x ++ ";\n"
pprintTerm n (OpenH c args) =
  indent n $ intercalate " " (show c : map pprintClosureArg args) ++ ";\n"
pprintTerm n (CaseH x _kind ks) =
  let branches = intercalate " | " (map (\ (c, k) -> show c ++ " -> " ++ show k) ks) in
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
pprintClosureArg (TypeArg s) = '@' : pprintSort s
pprintClosureArg (ValueArg x) = show x

pprintValue :: ValueH -> String
pprintValue (PairH x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue NilH = "()"
pprintValue (IntH i) = show i
pprintValue (StringValH s) = show s
pprintValue (CtorAppH capp) = pprintCtorApp capp

pprintCtorApp :: CtorAppH -> String
pprintCtorApp (BoolH b) = if b then "true" else "false"
pprintCtorApp (InlH x) = "inl(" ++ show x ++ ")"
pprintCtorApp (InrH y) = "inr(" ++ show y ++ ")"
pprintCtorApp ListNilH = "nil()"
pprintCtorApp (ListConsH x xs) = "cons(" ++ show x ++ ", " ++ show xs ++ ")"
pprintCtorApp (CtorApp c xs) = show c ++ "(" ++ intercalate ", " (map show xs) ++ ")"

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
pprintPrim (PrimConcatenate x y) = "prim_concatenate(" ++ show x ++ ", " ++ show y ++ ")"
pprintPrim (PrimStrlen x) = "prim_strlen(" ++ show x ++ ")"

pprintPlace :: Place -> String
pprintPlace (Place s x) = show x ++ " : " ++ pprintSort s

pprintParam :: ClosureParam -> String
pprintParam (PlaceParam p) = pprintPlace p
pprintParam (TypeParam aa k) = '@' : show aa ++ " : " ++ pprintKind k

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d _envPlace env) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ pprintEnvAlloc env ++ "\n"

pprintEnvAlloc :: EnvAlloc -> String
pprintEnvAlloc (EnvAlloc tyfields fields) =
  "{" ++ intercalate ", " (map pprintSort tyfields ++ map pprintAllocArg fields) ++ "}"

pprintAllocArg :: (Id, Name) -> String
pprintAllocArg (field, x) = show field ++ " = " ++ show x

pprintSort :: Sort -> String
pprintSort IntegerH = "int"
pprintSort BooleanH = "bool"
pprintSort UnitH = "unit"
pprintSort StringH = "string"
pprintSort (ListH t) = "list " ++ pprintSort t
pprintSort (ProductH t s) = "pair " ++ pprintSort t ++ " " ++ pprintSort s
pprintSort (SumH t s) = "sum " ++ pprintSort t ++ " " ++ pprintSort s
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
