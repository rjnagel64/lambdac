
-- | A module describing the structure and syntactic operations on the Hoist IR.
module Hoist.IR
    ( Id(..)
    , primeId
    , Unique(..)
    , Name(..)
    , Place(..)
    , TyVar(..)
    , CodeLabel(..)
    , FieldLabel(..)

    , Type(..)
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
    , substType
    , substTele

    , CodeDecl(..)
    , codeDeclName
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
    , PrimOp(..)
    , PrimIO(..)


    , Program(..)
    , Decl(..)
    , pprintProgram
    , pprintType
    , pprintKind
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Bifunctor
import Data.Int (Int64)
import Data.List (intercalate)


newtype Unique = Unique Int
  deriving (Eq, Ord)

instance Show Unique where
  show (Unique u) = show u


-- | An 'Id' is any type of identifier.
data Id = Id String Int
  deriving (Eq, Ord)

instance Show Id where
  show (Id x i) = x ++ show i

primeId :: Id -> Id
primeId (Id x i) = Id x (i+1)

-- | A 'Name' refers to a 'Place'. It is either a 'Place' in the local
-- scope, or in the environment scope.
data Name = LocalName Id | EnvName FieldLabel
  deriving (Eq, Ord)

instance Show Name where
  show (LocalName x) = show x
  show (EnvName x) = "@." ++ show x

-- | A 'Place' is a location that can hold a value. It has an identifier and a
-- sort that specifies what values can be stored there.
data Place = Place { placeType :: Type, placeName :: Id }

data TyVar = TyVar String Int
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa i) = aa ++ show i

prime :: TyVar -> TyVar
prime (TyVar aa i) = TyVar aa (i+1)

-- | 'CodeLabel's are used to reference top-level code definitions. In
-- particular, a closure is constructed by pairing a code name with an
-- appropriate closure environment.
data CodeLabel = CodeLabel String Unique

instance Eq CodeLabel where
  CodeLabel _ u1 == CodeLabel _ u2 = u1 == u2

instance Ord CodeLabel where
  compare (CodeLabel _ u1) (CodeLabel _ u2) = compare u1 u2

instance Show CodeLabel where
  show (CodeLabel d u) = '#' : d ++ "@" ++ show u


newtype TyCon = TyCon String
  deriving (Eq, Ord)

instance Show TyCon where
  show (TyCon tc) = tc

newtype Ctor = Ctor String
  deriving (Eq, Ord)

instance Show Ctor where
  show (Ctor c) = c

newtype FieldLabel = FieldLabel String
  deriving (Eq, Ord)

instance Show FieldLabel where
  show (FieldLabel f) = f



data Program = Program [Decl] TermH

data Decl
  = DeclCode CodeDecl
  | DeclData DataDecl


data CodeDecl
  = CodeDecl CodeLabel (Id, EnvDecl) [ClosureParam] TermH

codeDeclName :: CodeDecl -> CodeLabel
codeDeclName (CodeDecl c _ _ _) = c 

data EnvDecl = EnvDecl [(TyVar, Kind)] [(FieldLabel, Type)]

data ClosureParam = PlaceParam Place | TypeParam TyVar Kind


data DataDecl
  = DataDecl TyCon Kind [CtorDecl]

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
  = CtorDecl Ctor [(TyVar, Kind)] [(Id, Type)]


-- | A 'Type' describes the runtime layout of a value. It is static information.
data Type
  = AllocH TyVar
  | IntegerH
  | BooleanH
  | UnitH
  | StringH
  | CharH
  | ProductH Type Type
  | ClosureH ClosureTele
  | RecordH [(FieldLabel, Type)]
  | TyConH TyCon
  | TyAppH Type Type
  | TokenH

-- It's a bit unfortunate, but I do need to have separate telescopes for
-- parameters and types. The difference is that parameters need names for each
-- value, but closure types ignore value parameter names, and also cannot infer
-- those names.
newtype ClosureTele = ClosureTele [TeleEntry]

data TeleEntry
  = ValueTele Type
  | TypeTele TyVar Kind

instance Eq Type where
  (==) = equalType emptyAE

data Kind = Star | KArr Kind Kind
  deriving (Eq)

asTyConApp :: Type -> Maybe TyConApp
asTyConApp (TyConH tc) = Just (TyConApp tc [])
asTyConApp (TyAppH t s) = go t [s]
  where
    go (TyAppH t' s') acc = go t' (s' : acc)
    go (TyConH tc) acc = Just (TyConApp tc acc)
    -- Hmm. is 'f Int Bool Char' a TyConApp? I don't think so. You can't
    -- construct ctors or case on it.
    go _ _ = Nothing
asTyConApp _ = Nothing

fromTyConApp :: TyConApp -> Type
fromTyConApp (TyConApp tc args) = foldl TyAppH (TyConH tc) args

data TyConApp
  = TyConApp TyCon [Type]




data TermH
  -- 'let x : int = 17 in e'
  = LetValH Place ValueH TermH
  -- 'let z : bool = prim_int64gt(x, y) in e'
  | LetPrimH Place PrimOp TermH
  -- 'let s1 : token#, x : t <- prim_putLine(s0, msg) in e'
  | LetBindH Place Place PrimIO TermH
  -- 'let x : int64 = y .fst in e'
  | LetProjectH Place Name Projection TermH
  -- 'halt @bool x'
  | HaltH Type Name
  -- 'call f (x, @int, z, $string_info)'
  | OpenH Name [ClosureArg]
  -- 'if x then k1 else k2'
  | IfH Name Name Name
  -- 'case x of { c1 -> k1 | c2 -> k2 | ... }'
  | CaseH Name TyConApp [(Ctor, Name)]
  -- 'letrec (f1 : closure(ss) = #f1 { env1 })+ in e'
  -- Closures may be mutually recursive, so they are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

data Projection = ProjectFst | ProjectSnd | ProjectField FieldLabel

data ClosureArg = ValueArg Name | TypeArg Type

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
-- 'pack <t+, { (l = x)+ }> as _'
data EnvAlloc
  = EnvAlloc {
    envAllocTypeArgs :: [Type]
  , envAllocValueArgs :: [(FieldLabel, Name)]
  }

data ValueH
  = IntH Int64
  | BoolH Bool
  | StringValH String
  | CharValH Char
  | PairH Name Name
  | NilH
  | WorldToken
  | RecordValH [(FieldLabel, Name)]
  | CtorAppH Ctor [Type] [Name]

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

freeTyVars :: Type -> Set TyVar
freeTyVars s = runFV (ftv s) Set.empty Set.empty

ftv :: Type -> FV
ftv (AllocH aa) = unitFV aa
ftv (TyConH _) = mempty
ftv UnitH = mempty
ftv IntegerH = mempty
ftv BooleanH = mempty
ftv StringH = mempty
ftv CharH = mempty
ftv TokenH = mempty
ftv (ProductH t s) = ftv t <> ftv s
ftv (RecordH fs) = foldMap (ftv . snd) fs
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
equalType :: AE -> Type -> Type -> Bool
equalType ae (AllocH aa) (AllocH bb) = lookupAE ae aa bb
equalType _ (AllocH _) _ = False
equalType _e (TyConH tc1) (TyConH tc2) = tc1 == tc2
equalType _ (TyConH _) _ = False
equalType _ IntegerH IntegerH = True
equalType _ IntegerH _ = False
equalType _ BooleanH BooleanH = True
equalType _ BooleanH _ = False
equalType _ UnitH UnitH = True
equalType _ UnitH _ = False
equalType _ StringH StringH = True
equalType _ StringH _ = False
equalType _ CharH CharH = True
equalType _ CharH _ = False
equalType _ TokenH TokenH = True
equalType _ TokenH _ = False
equalType ae (ProductH s1 s2) (ProductH t1 t2) = equalType ae s1 t1 && equalType ae s2 t2
equalType _ (ProductH _ _) _ = False
equalType ae (RecordH fs1) (RecordH fs2) = go fs1 fs2
  where
    go [] [] = True
    go ((f1, t1):fs1') ((f2, t2):fs2') = f1 == f2 && equalType ae t1 t2 && go fs1' fs2'
    go _ _ = False
equalType _ (RecordH _) _ = False
equalType ae (TyAppH s1 s2) (TyAppH t1 t2) = equalType ae s1 t1 && equalType ae s2 t2
equalType _ (TyAppH _ _) _ = False
equalType ae (ClosureH ss) (ClosureH ts) = equalTele ae ss ts
equalType _ (ClosureH _) _ = False

equalTele :: AE -> ClosureTele -> ClosureTele -> Bool
equalTele ae0 (ClosureTele tele) (ClosureTele tele') = go ae0 tele tele'
  where
    go _ [] [] = True
    go ae (ValueTele s : ls) (ValueTele t : rs) = equalType ae s t && go ae ls rs
    go _ (ValueTele _ : _) (_ : _) = False
    go ae (TypeTele aa k1 : ls) (TypeTele bb k2 : rs) =
      k1 == k2 && go (bindAE aa bb ae) ls rs
    go _ (TypeTele _ _ : _) (_ : _) = False
    go _ (_ : _) [] = False
    go _ [] (_ : _) = False


-- | A substitution maps free type variables to sorts, avoiding free variable
-- capture when it passes under type variable binders.
data Subst = Subst { substScope :: Set TyVar, substMapping :: Map TyVar Type }

-- | Construct a singleton substitution, @[aa := s]@.
singleSubst :: TyVar -> Type -> Subst
singleSubst aa s =
  -- We must not capture any free variable of 's', so the scope is intially set
  -- to 'FTV(s)'.
  Subst { substScope = freeTyVars s, substMapping = Map.singleton aa s }

listSubst :: [(TyVar, Type)] -> Subst
listSubst xs = Subst { substScope = foldMap (freeTyVars . snd) xs, substMapping = Map.fromList xs }

-- | Pass a substitution under a variable binder, returning the updated
-- substitution, and a new variable binder.
substBind :: Subst -> TyVar -> (Subst, TyVar)
substBind (Subst sc sub) aa =
  if Set.notMember aa sc then
    (Subst (Set.insert aa sc) (Map.delete aa sub), aa)
  else
    go (prime aa)
  where
    go aa' =
      if Set.notMember aa' sc then
        (Subst (Set.insert aa' sc) (Map.insert aa (AllocH aa') sub), aa')
      else
        go (prime aa')

lookupSubst :: TyVar -> Subst -> Maybe Type
lookupSubst aa (Subst _ sub) = Map.lookup aa sub

-- | Apply a substitution to a sort.
substType :: Subst -> Type -> Type
substType sub (AllocH aa) = case lookupSubst aa sub of
  Nothing -> AllocH aa
  Just s -> s
substType _ (TyConH tc) = TyConH tc
substType _ IntegerH = IntegerH
substType _ BooleanH = BooleanH
substType _ UnitH = UnitH
substType _ StringH = StringH
substType _ CharH = CharH
substType _ TokenH = TokenH
substType sub (ProductH s t) = ProductH (substType sub s) (substType sub t)
substType sub (RecordH fs) = RecordH (map (second (substType sub)) fs)
substType sub (TyAppH s t) = TyAppH (substType sub s) (substType sub t)
substType sub (ClosureH tele) = ClosureH (substTele sub tele)

substTele :: Subst -> ClosureTele -> ClosureTele
substTele subst (ClosureTele tele) = ClosureTele (go subst tele)
  where
    go _ [] = []
    go sub (ValueTele s : tele') = ValueTele (substType sub s) : go sub tele'
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
pprintClosureDecl n (CodeDecl f (name, EnvDecl aas fs) params e) =
  indent n ("code " ++ show f ++ "[" ++ tyParams ++ "](" ++ envParam ++ "; " ++ valueParams ++ ") =\n") ++
  pprintTerm (n+2) e
  where
    tyParams = intercalate ", " typeFields
    typeFields = map (\ (aa, k) -> "@" ++ show aa ++ " : " ++ pprintKind k) aas
    envParam = show name ++ " : {" ++ intercalate ", " (map pprintEnvField fs) ++ "}"
    pprintEnvField (x, s) = show x ++ " : " ++ pprintType s
    valueParams = intercalate ", " (map pprintParam params)

pprintDataDecl :: Int -> DataDecl -> String
pprintDataDecl n (DataDecl tc k ctors) =
  indent n ("data " ++ show tc ++ " : " ++ pprintKind k ++ " where\n") ++
  unlines (map (pprintCtorDecl (n+2)) ctors)

pprintCtorDecl :: Int -> CtorDecl -> String
pprintCtorDecl n (CtorDecl c tys args) =
  indent n (show c ++ "(" ++ intercalate ", " (map g tys ++ map f args) ++ ");")
  where
    g (aa, k) = "@" ++ show aa ++ " : " ++ pprintKind k
    f (x, s) = show x ++ " : " ++ pprintType s

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH s x) = indent n $ "HALT @" ++ pprintType s ++ " " ++ show x ++ ";\n"
pprintTerm n (OpenH c args) =
  indent n $ intercalate " " (show c : map pprintClosureArg args) ++ ";\n"
pprintTerm n (IfH x k1 k2) =
  indent n $ "if " ++ show x ++ " then " ++ show k1 ++ " else " ++ show k2
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
    proj (ProjectField f) = show f
pprintTerm n (LetPrimH x p e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintPrim p ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetBindH p1 p2 prim e) =
  indent n ("let " ++ ps ++ " = " ++ pprintPrimIO prim ++ ";\n") ++ pprintTerm n e
  where ps = pprintPlace p1 ++ ", " ++ pprintPlace p2
pprintTerm n (AllocClosure cs e) =
  indent n "let\n" ++ concatMap (pprintClosureAlloc (n+2)) cs ++ indent n "in\n" ++ pprintTerm n e

pprintClosureArg :: ClosureArg -> String
pprintClosureArg (TypeArg s) = '@' : pprintType s
pprintClosureArg (ValueArg x) = show x

pprintValue :: ValueH -> String
pprintValue (PairH x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (RecordValH []) = "{}"
pprintValue (RecordValH xs) = "{ " ++ intercalate ", " (map pprintField xs) ++ " }"
  where pprintField (f, x) = show f ++ " = " ++ show x
pprintValue NilH = "()"
pprintValue (IntH i) = show i
pprintValue (BoolH b) = if b then "true" else "false"
pprintValue (StringValH s) = show s
pprintValue (CharValH c) = show c
pprintValue WorldToken = "WORLD#"
pprintValue (CtorAppH c ss xs) =
  show c ++ "(" ++ intercalate ", @" (map pprintType ss) ++ ", " ++ intercalate ", " (map show xs) ++ ")"

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
pprintPlace (Place s x) = show x ++ " : " ++ pprintType s

pprintParam :: ClosureParam -> String
pprintParam (PlaceParam p) = pprintPlace p
pprintParam (TypeParam aa k) = '@' : show aa ++ " : " ++ pprintKind k

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d _envPlace env) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ pprintEnvAlloc env ++ "\n"

pprintEnvAlloc :: EnvAlloc -> String
pprintEnvAlloc (EnvAlloc tyfields fields) =
  "{" ++ intercalate ", " (map pprintType tyfields ++ map pprintAllocArg fields) ++ "}"

pprintAllocArg :: (FieldLabel, Name) -> String
pprintAllocArg (field, x) = show field ++ " = " ++ show x

pprintType :: Type -> String
pprintType IntegerH = "int"
pprintType BooleanH = "bool"
pprintType UnitH = "unit"
pprintType StringH = "string"
pprintType CharH = "char"
pprintType TokenH = "token#"
pprintType (ProductH t s) = "pair " ++ pprintType t ++ " " ++ pprintType s
pprintType (TyAppH t s) = pprintType t ++ " " ++ pprintType s
pprintType (ClosureH tele) = "closure(" ++ pprintTele tele ++ ")"
pprintType (RecordH []) = "{}"
pprintType (RecordH xs) = "{ " ++ intercalate ", " (map pprintField xs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintType t
pprintType (AllocH aa) = show aa
pprintType (TyConH tc) = show tc

pprintTele :: ClosureTele -> String
pprintTele (ClosureTele ss) = intercalate ", " (map f ss)
  where
    f (ValueTele s) = pprintType s
    f (TypeTele aa k) = "forall " ++ show aa ++ " : " ++ pprintKind k

pprintKind :: Kind -> String
pprintKind Star = "*"
pprintKind (KArr Star k2) = "* -> " ++ pprintKind k2
pprintKind (KArr k1 k2) = "(" ++ pprintKind k1 ++ ") -> " ++ pprintKind k2
