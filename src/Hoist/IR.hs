
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

    , Kind(..)

    , Subst
    , singleSubst
    , substSort

    , CodeDecl(..)
    , codeDeclName
    , codeDeclTele
    , EnvDecl(..)
    , ClosureParam(..)

    , TermH(..)
    , Projection(..)
    , ClosureArg(..)
    , CaseKind(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , EnvAllocValueArg(..)
    , ValueH(..)
    , CtorAppH(..)
    , Ctor(..)
    , PrimOp(..)


    , Program(..)
    , Decl(..)
    , pprintProgram
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
  show (CodeLabel d) = d


newtype TyCon = TyCon String

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
  = DataDecl TyCon Kind [(TyVar, Kind)] [CtorDecl]

data CtorDecl
  -- Can't just use 'ClosureTele' here, because ctor applications actually return a value.
  -- (Also, I don't support existential ADTs yet, so I can't have TypeTele in here.)
  --
  -- Also, I don't have GADTs, so the return type is redundant (it's just the
  -- tycon applied to the parameters)
  = CtorDecl Ctor [Sort]


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

-- asTyConApp :: Sort -> Maybe TyConApp

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

data Kind = Star
  deriving (Eq)




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
  | CaseH Name CaseKind [(Ctor, Name)]
  -- 'letrec (f1 : closure(ss) = #f1 { env1 })+ in e'
  -- Closures may be mutually recursive, so they are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

data Projection = ProjectFst | ProjectSnd

data ClosureArg = ValueArg Name | TypeArg Sort

-- Consider renaming 'CaseKind' to 'TyConApp'.
data CaseKind = CaseBool | CaseSum Sort Sort | CaseList Sort

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: Place
  , closureDecl :: CodeLabel
  , closureEnvPlace :: Id
  , closureEnv :: EnvAlloc
  }

data EnvAlloc
  = EnvAlloc {
    -- Hmm. While I definitely do not want a bunch of info args, I may still
    -- want to have a list of type/tyvar arguments here (for type-checking
    -- purposes, since EnvAlloc represents constructing a value of type 'exists
    -- aa+. (singleton aa)+ × t+', though the type portions get erased.)
    envAllocValueArgs :: [EnvAllocValueArg]
  }

data EnvAllocValueArg = EnvValueArg Id Name

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
ftv UnitH = mempty
ftv IntegerH = mempty
ftv BooleanH = mempty
ftv StringH = mempty
ftv (ListH t) = ftv t
ftv (ProductH t s) = ftv t <> ftv s
ftv (SumH t s) = ftv t <> ftv s
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

-- | Apply a substitution to a sort.
substSort :: Subst -> Sort -> Sort
substSort sub (AllocH aa) = case Map.lookup aa (substMapping sub) of
  Nothing -> AllocH aa
  Just s -> s
substSort _ IntegerH = IntegerH
substSort _ BooleanH = BooleanH
substSort _ UnitH = UnitH
substSort _ StringH = StringH
substSort sub (ProductH s t) = ProductH (substSort sub s) (substSort sub t)
substSort sub (SumH s t) = SumH (substSort sub s) (substSort sub t)
substSort sub (ListH t) = ListH (substSort sub t)
substSort sub (ClosureH (ClosureTele tele)) = ClosureH (ClosureTele (substTele sub tele))

substTele :: Subst -> [TeleEntry] -> [TeleEntry]
substTele _ [] = []
substTele sub (ValueTele s : tele) = ValueTele (substSort sub s) : substTele sub tele
substTele sub (TypeTele aa k1 : tele) = case substBind sub aa of
  (sub', aa') -> TypeTele aa' k1 : substTele sub' tele


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintProgram :: Program -> String
pprintProgram (Program ds srcH) = pprintDecls ds ++ ";;\n" ++ pprintTerm 0 srcH

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
pprintCtorApp (InlH x) = "inl " ++ show x
pprintCtorApp (InrH y) = "inr " ++ show y
pprintCtorApp ListNilH = "nil"
pprintCtorApp (ListConsH x xs) = "cons " ++ show x ++ " " ++ show xs

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

pprintDecls :: [Decl] -> String
pprintDecls ds = concatMap pprintDecl ds
  where
    pprintDecl (DeclCode cd) = pprintClosureDecl 0 cd
    pprintDecl (DeclData dd) = error "not implemented: ppr DataDecl"

pprintClosureDecl :: Int -> CodeDecl -> String
pprintClosureDecl n (CodeDecl f (name, EnvDecl is fs) params e) =
  indent n ("code " ++ show f ++ " (" ++ envParam ++ "; " ++ intercalate ", " (map pprintParam params) ++ ") =\n") ++
  pprintTerm (n+2) e
  where
    envParam = show name ++ " : {" ++ intercalate ", " (infoFields ++ valueFields) ++ "}"
    infoFields = map (\ (aa, k) -> "@" ++ show aa) is
    valueFields = map pprintPlace fs

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d _envPlace env) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ pprintEnvAlloc env ++ "\n"

pprintEnvAlloc :: EnvAlloc -> String
pprintEnvAlloc (EnvAlloc fields) =
  "{" ++ intercalate ", " (map pprintAllocArg fields) ++ "}"

pprintAllocArg :: EnvAllocValueArg -> String
pprintAllocArg (EnvValueArg field x) = show field ++ " = " ++ show x

pprintSort :: Sort -> String
pprintSort IntegerH = "int"
pprintSort BooleanH = "bool"
pprintSort UnitH = "unit"
pprintSort StringH = "string"
pprintSort (ListH t) = "list " ++ pprintSort t
pprintSort (ProductH t s) = "pair " ++ pprintSort t ++ " " ++ pprintSort s
pprintSort (SumH t s) = "sum " ++ pprintSort t ++ " " ++ pprintSort s
pprintSort (ClosureH tele) = "closure(" ++ pprintTele tele ++ ")"
pprintSort (AllocH aa) = show aa

pprintTele :: ClosureTele -> String
pprintTele (ClosureTele ss) = intercalate ", " (map f ss)
  where
    f (ValueTele s) = pprintSort s
    f (TypeTele aa k) = "forall " ++ show aa ++ " : " ++ pprintKind k

pprintKind :: Kind -> String
pprintKind Star = "*"
