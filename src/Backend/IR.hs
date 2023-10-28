
module Backend.IR
    ( Id(..)
    , Unique(..)
    , Name(..)
    , Place(..)
    , TyVar(..)
    , GlobalLabel(..)
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

    , EnvDecl(..)
    , CodeDecl(..)
    , codeDeclName
    , codeDeclTele
    , ClosureParam(..)
    , ConstDecl(..)

    , DataDecl(..)
    , TyCon(..)
    , CtorDecl(..)
    , Ctor(..)

    , TermH(..)
    , Projection(..)
    , ClosureArg(..)
    , CaseAlt(..)
    , IntCaseAlt(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , ValueH(..)
    , PrimOp(..)
    , PrimIO(..)
    , CtorArg(..)

    , Program(..)
    , Decl(..)
    , pprintProgram
    , pprintType
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


-- | A thunk type is a calling convention for closures: the set of arguments
-- that must be provided to open it. This information is used to generate
-- trampolined tail calls.
--
-- Because 'ThunkType' is mostly concerned with the call site, it does not have
-- a binding structure. (Or does it?)
data ThunkType = ThunkType { thunkArgs :: [ThunkArg] }

data ThunkArg
  = ThunkValueArg Type
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
    tycode :: Type -> String
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



newtype Unique = Unique Int
  deriving (Eq, Ord)

instance Show Unique where
  show (Unique u) = show u


-- | An 'Id' is any type of identifier.
data Id = Id String Unique
  deriving (Eq, Ord)

instance Show Id where
  show (Id x u) = x ++ "_" ++ show u

-- | A 'Name' references some in-scope value binding. It can be either a name
-- in the local scope, or it can be a reference to some field from the
-- environment. 
data Name = LocalName Id | EnvName Id FieldLabel | FieldRef Name FieldLabel
  deriving (Eq, Ord)

instance Show Name where
  show (LocalName x) = show x
  show (EnvName envp x) = show envp ++ "." ++ show x
  show (FieldRef x l) = show x ++ "." ++ show l

-- | A 'Place' is a location that can hold a value. It has an identifier and a
-- sort that specifies what values can be stored there.
data Place = Place { placeType :: Type, placeName :: Id }

data TyVar = TyVar String Int
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa i) = aa ++ show i

prime :: TyVar -> TyVar
prime (TyVar aa i) = TyVar aa (i+1)

-- | 'GlobalLabel's are used to reference top-level definitions. In particular,
-- a closure is constructed by pairing a global code label with an appropriate
-- closure environment.
data GlobalLabel = GlobalLabel String Unique
  deriving (Eq, Ord)

instance Show GlobalLabel where
  show (GlobalLabel l u) = l ++ "_" ++ show u


newtype TyCon = TyCon String
  deriving (Eq, Ord)

instance Show TyCon where
  show (TyCon tc) = tc

data Ctor = Ctor { ctorTyCon :: TyCon, ctorName :: String, ctorDiscriminant :: Int }
  deriving (Eq, Ord)

instance Show Ctor where
  show (Ctor tc c _) = show tc ++ "::" ++ c

newtype FieldLabel = FieldLabel String
  deriving (Eq, Ord)

instance Show FieldLabel where
  show (FieldLabel f) = f



data Program = Program [Decl] TermH

data Decl
  = DeclData DataDecl
  | DeclEnv EnvDecl
  | DeclCode CodeDecl
  | DeclConst ConstDecl


data EnvDecl
  = EnvDecl TyCon [(FieldLabel, Type)]

data CodeDecl
  -- The [(TyVar, Kind)] here is never used for anything.
  -- (Only for the pretty-printing Backend.IR, which I am already inclined to
  -- remove)
  = CodeDecl GlobalLabel [(TyVar, Kind)] (Id, TyCon) [ClosureParam] TermH

codeDeclName :: CodeDecl -> GlobalLabel
codeDeclName (CodeDecl c _ _ _ _) = c 

codeDeclTele :: CodeDecl -> ClosureTele
codeDeclTele (CodeDecl _ _ _ params _) = ClosureTele (map f params)
  where
    f (PlaceParam p) = ValueTele (placeType p)
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
  = CtorDecl Ctor [(TyVar, Kind)] [(FieldLabel, Type)]


data ConstDecl
  -- ConstClosure l0 l1 represents a C declaration:
  -- struct closure *l0 = STATIC_CLOSURE(l1, the_empty_env);
  = ConstClosure GlobalLabel GlobalLabel -- assume environment == empty


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
  | TyRecordH [(FieldLabel, Type)]
  | TyConH TyCon
  | TyAppH Type Type
  | TokenH
  -- | CodeH ClosureTele -- represents 'struct code X;', where struct code { void (*enter(void) };
  -- Code decl declares a global label for a value of type 'CodeH _'
  -- (Does a CodeH type require the pseudo-forall? In Hoist maybe, in Lower probably not.)

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

data TyConApp = TyConApp TyCon [Type]




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
  | HaltH Type Name
  -- 'call f (x, @int, z)', annotated with calling convention
  | OpenH ThunkType Name [ClosureArg]
  -- 'case x of { c1 -> k1 | c2 -> k2 | ... }'
  | CaseH Name TyConApp [CaseAlt]
  -- 'case x of { 17 -> k1 | 32 -> k2 | ... | default -> kd }'
  | IntCaseH Name [IntCaseAlt]

data Projection = ProjectFst | ProjectSnd | ProjectField FieldLabel

data ClosureArg = ValueArg Name | TypeArg Type

data CaseAlt = CaseAlt Ctor ThunkType Name

-- All thunktypes should be no-arg, ThunkType []
data IntCaseAlt = IntCaseAlt Int64 ThunkType Name

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: Place
  , closureDecl :: GlobalLabel
  , closureCodeInst :: [Type]
  , closureEnvRef :: Id
  }

data EnvAlloc
  = EnvAlloc Id TyCon [(FieldLabel, Name)]


data ValueH
  = IntH Int64
  | BoolH Bool
  | StringValH String
  | CharValH Char
  | PairH Name Name
  | NilH
  | WorldToken
  | RecordH [(FieldLabel, Name)]
  | CtorAppH Ctor [Type] [Name]

-- TODO: refine CtorAppH. Remove type arguments, replace value args with these:
-- (Could also use these for PairH args)
data CtorArg
  = NormalArg Name -- ^ x
  | UpCastArg Name -- ^ AS_ALLOC(x)
  | DownCastArg Type Name -- ^ CAST_int64_value(x)

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
equalType ae (TyRecordH fs1) (TyRecordH fs2) = go fs1 fs2
  where
    go [] [] = True
    go ((f1, t1):fs1') ((f2, t2):fs2') = f1 == f2 && equalType ae t1 t2 && go fs1' fs2'
    go _ _ = False
equalType _ (TyRecordH _) _ = False
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
substType sub (TyRecordH fs) = TyRecordH (map (second (substType sub)) fs)
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
-- Hmm. This is just copy-pasted from Hoist. I don't actually use it for anything?
-- I don't think backend-internal IRs really need to be printable.

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
    pprintDecl (DeclConst cd) = pprintConstDecl 0 cd

pprintEnvDecl :: Int -> EnvDecl -> String
pprintEnvDecl n (EnvDecl l fields) =
  indent n ("environment " ++ show l ++ "::Env = {" ++ intercalate ", " (map pprintEnvField fields) ++ "}\n")
  where pprintEnvField (x, s) = show x ++ " : " ++ pprintType s

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
    f (x, s) = show x ++ " : " ++ pprintType s
    g (aa, k) = "@" ++ show aa ++ " : " ++ pprintKind k

pprintConstDecl :: Int -> ConstDecl -> String
pprintConstDecl n (ConstClosure l l') = indent n ("const " ++ show l ++ " = #" ++ show l' ++ " {}")

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH s x) = indent n $ "HALT @" ++ pprintType s ++ " " ++ show x ++ ";\n"
pprintTerm n (OpenH _ty c args) =
  indent n $ intercalate " " (show c : map pprintClosureArg args) ++ ";\n"
pprintTerm n (CaseH x _kind alts) =
  indent n $ "case " ++ show x ++ " of " ++ intercalate " | " (map pprintAlt alts) ++ ";\n"
  where pprintAlt (CaseAlt c _ty k) = show c ++ " -> " ++ show k
pprintTerm n (IntCaseH x alts) =
  indent n $ "case " ++ show x ++ " of " ++ intercalate " | " (map pprintAlt alts) ++ ";\n"
  where pprintAlt (IntCaseAlt i _ty k) = show i ++ " -> " ++ show k
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
pprintClosureArg (TypeArg s) = '@' : pprintType s
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

pprintEnvAlloc :: Int -> EnvAlloc -> String
pprintEnvAlloc n (EnvAlloc p tc fs) =
  indent n $ show p ++ " : " ++ show tc ++ " = {" ++ intercalate ", " (map pprintAllocArg fs) ++ "}\n"

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d tys env) =
  indent n $ pprintPlace p ++ " = <<" ++ show d ++ " " ++ intercalate " @" (map pprintType tys) ++ ", " ++ show env ++ ">>\n"

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
pprintType (TyRecordH []) = "{}"
pprintType (TyRecordH fs) = "{ " ++ intercalate ", " (map pprintField fs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintType t
pprintType (TyAppH t s) = pprintType t ++ " " ++ pprintType s
pprintType (ClosureH tele) = "closure(" ++ pprintTele tele ++ ")"
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
