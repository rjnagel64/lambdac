
-- | A module describing the structure and syntactic operations on the Hoist IR.
module Hoist.IR
    ( Id(..)
    , Name(..)
    , Place(..)
    , InfoPlace(..)
    , TyVar(..)
    , ClosureName(..)

    , Sort(..)
    , ClosureTele(..)
    , TeleEntry(..)
    , Info(..)

    , Subst
    , singleSubst
    , substSort

    , ClosureDecl(..)
    , closureDeclName
    , EnvDecl(..)
    , ClosureParam(..)

    , TermH(..)
    , Projection(..)
    , ClosureArg(..)
    , CaseKind(..)
    , ClosureAlloc(..)
    , EnvAlloc(..)
    , EnvAllocInfoArg(..)
    , EnvAllocValueArg(..)
    , ValueH(..)
    , PrimOp(..)

    , Program(..)
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

-- | A 'InfoPlace' is a location that can hold a @type_info@.
--
-- Hmm. Right now, @InfoPlace (Id "aa")@ beasically means `aa : info aa`. Aside
-- from muddling term/info and type namespaces, it also overlaps with
-- InfoPlace2 (denoting `i : info t`.
data InfoPlace = InfoPlace { infoName :: Id }

data TyVar = TyVar Id
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa) = show aa

-- | 'ClosureName's are used to refer to top-level functions and continuations.
-- They are introduced by (hoisting) function/continuation closure bindings,
-- and used when allocating function/continuation closures.
newtype ClosureName = ClosureName String
  deriving (Eq, Ord)

instance Show ClosureName where
  show (ClosureName d) = d



-- | A 'Sort' describes the runtime layout of a value. It is static information.
data Sort
  = AllocH TyVar
  | IntegerH
  | BooleanH
  | UnitH
  | SumH
  | StringH
  | ProductH Sort Sort
  | ListH Sort
  | ClosureH ClosureTele

-- It's a bit unfortunate, but I do need to have separate telescopes for
-- parameters and types. The difference is that parameters need names for each
-- value, but closure types ignore value parameter names, and also cannot infer
-- those names.
newtype ClosureTele = ClosureTele [TeleEntry]

data TeleEntry
  = ValueTele Sort
  | TypeTele TyVar

instance Eq Sort where
  (==) = equalSort emptyAE


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
  -- @string_info@
  | StringInfo
  -- @pair_info@
  | ProductInfo
  -- @closure_info@
  | ClosureInfo
  -- @list_info@
  | ListInfo


data ClosureDecl
  = ClosureDecl ClosureName (Id, EnvDecl) [ClosureParam] TermH

closureDeclName :: ClosureDecl -> ClosureName
closureDeclName (ClosureDecl c _ _ _) = c 

data EnvDecl = EnvDecl [(Id, TyVar)] [Place]

-- Idea: Introduce InfoParam, and slowly migrate to use it wherever necessary.
-- Maybe rename TypeParam to TypeInfoParam, then refactor it out of existence.
data ClosureParam = PlaceParam Place | TypeParam TyVar | InfoParam Id Sort



data TermH
  = LetValH Place ValueH TermH
  | LetPrimH Place PrimOp TermH
  -- 'let value x = fst y in e'
  | LetProjectH Place Name Projection TermH
  | HaltH Sort Name Info
  | OpenH Name [ClosureArg]
  | CaseH Name CaseKind [Name]
  -- Closures may be mutually recursive, so they are allocated as a group.
  | AllocClosure [ClosureAlloc] TermH

data Projection = ProjectFst | ProjectSnd

-- TODO: I don't like OpaqueArg.
-- It is currently necessary because ThunkType:s can have free type variables.
-- An alternate method would be to add a "pseudo-forall" to the thunk type, so
-- that it is closed and the extra info args can be passed up front.
--
-- (This is the "closed thunk types" proposal)
-- TODO: Rename ClosureArg to CallArg? They can be used for PrimOps, too I think.
data ClosureArg = ValueArg Name | TypeArg Info | OpaqueArg Name Info

data CaseKind = CaseBool | CaseSum Sort Sort | CaseList Sort

data ClosureAlloc
  = ClosureAlloc {
    closurePlace :: Place
  , closureDecl :: ClosureName
  , closureEnvPlace :: Id
  , closureEnv :: EnvAlloc
  }

data EnvAlloc
  = EnvAlloc {
    envAllocInfoArgs :: [EnvAllocInfoArg]
  , envAllocValueArgs :: [EnvAllocValueArg]
  }

data EnvAllocInfoArg = EnvInfoArg Id Info

data EnvAllocValueArg = EnvValueArg Id Name

data ValueH
  = IntH Int64
  | BoolH Bool
  | PairH Info Info Name Name
  | NilH
  | InlH Info Name
  | InrH Info Name
  | ListNilH
  | ListConsH Info Name Name
  | StringValH String

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


data Program = Program [ClosureDecl] TermH


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
ftv SumH = mempty
ftv StringH = mempty
ftv (ListH t) = ftv t
ftv (ProductH t s) = ftv t <> ftv s
ftv (ClosureH tele) = ftvTele tele

ftvTele :: ClosureTele -> FV
ftvTele (ClosureTele tele) = go tele
  where
    go [] = mempty
    go (ValueTele s : rest) = ftv s <> go rest
    go (TypeTele aa : rest) = bindFV aa (go rest)
    -- go (InfoTele s : rest) = ftv s <> go rest

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
equalSort _ SumH SumH = True
equalSort _ SumH _ = False
equalSort _ StringH StringH = True
equalSort _ StringH _ = False
equalSort ae (ProductH s1 s2) (ProductH t1 t2) = equalSort ae s1 t1 && equalSort ae s2 t2
equalSort _ (ProductH _ _) _ = False
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
    go ae (TypeTele aa : ls) (TypeTele bb : rs) =
      go (bindAE aa bb ae) ls rs
    go _ (TypeTele _ : _) (_ : _) = False
    go _ (_ : _) [] = False
    go _ [] (_ : _) = False


-- | A substitution maps free type variables to sorts, avoiding free variable
-- capture when it passes under type variable binders.
data Subst = Subst { substScope :: Set TyVar, substMapping :: Map TyVar Sort }

-- | Construct the empty/identity substitution.
emptySubst :: Subst
emptySubst = Subst { substScope = Set.empty, substMapping = Map.empty }

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
substSort _ SumH = SumH
substSort _ StringH = StringH
substSort sub (ProductH s t) = ProductH (substSort sub s) (substSort sub t)
substSort sub (ListH t) = ListH (substSort sub t)
substSort sub (ClosureH (ClosureTele tele)) = ClosureH (ClosureTele (substTele sub tele))

substTele :: Subst -> [TeleEntry] -> [TeleEntry]
substTele _ [] = []
substTele sub (ValueTele s : tele) = ValueTele (substSort sub s) : substTele sub tele
substTele sub (TypeTele aa : tele) = case substBind sub aa of
  (sub', aa') -> TypeTele aa' : substTele sub' tele


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintProgram :: Program -> String
pprintProgram (Program cs srcH) = pprintClosures cs ++ ";;\n" ++ pprintTerm 0 srcH

pprintTerm :: Int -> TermH -> String
pprintTerm n (HaltH _ x _) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (OpenH c args) =
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
pprintClosureArg (TypeArg i) = '@' : pprintInfo i
pprintClosureArg (ValueArg x) = show x
pprintClosureArg (OpaqueArg x i) = show x ++ "@" ++ pprintInfo i

pprintValue :: ValueH -> String
pprintValue (PairH _ _ x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue NilH = "()"
pprintValue (IntH i) = show i
pprintValue (BoolH b) = if b then "true" else "false"
pprintValue (InlH _ x) = "inl " ++ show x
pprintValue (InrH _ y) = "inr " ++ show y
pprintValue ListNilH = "nil"
pprintValue (ListConsH _ x xs) = "cons " ++ show x ++ " " ++ show xs
pprintValue (StringValH s) = show s

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

pprintInfoPlace :: InfoPlace -> String
pprintInfoPlace (InfoPlace aa) = '@' : show aa

pprintParam :: ClosureParam -> String
pprintParam (PlaceParam p) = pprintPlace p
pprintParam (TypeParam aa) = '@' : show aa

pprintClosures :: [ClosureDecl] -> String
pprintClosures cs = concatMap (pprintClosureDecl 0) cs

pprintClosureDecl :: Int -> ClosureDecl -> String
pprintClosureDecl n (ClosureDecl f (name, EnvDecl is fs) params e) =
  indent n ("code " ++ show f ++ " (" ++ envParam ++ "; " ++ intercalate ", " (map pprintParam params) ++ ") =\n") ++
  pprintTerm (n+2) e
  where
    envParam = show name ++ " : {" ++ intercalate ", " (infoFields ++ valueFields) ++ "}"
    infoFields = map (\ (i, aa) -> '@' : show i ++ " : info " ++ show aa) is
    valueFields = map pprintPlace fs

pprintClosureAlloc :: Int -> ClosureAlloc -> String
pprintClosureAlloc n (ClosureAlloc p d _envPlace env) =
  indent n $ pprintPlace p ++ " = " ++ show d ++ " " ++ pprintEnvAlloc env ++ "\n"

pprintEnvAlloc :: EnvAlloc -> String
pprintEnvAlloc (EnvAlloc info fields) =
  "{" ++ intercalate ", " (map pprintAllocInfo info ++ map pprintAllocArg fields) ++ "}"

pprintAllocInfo :: EnvAllocInfoArg -> String
pprintAllocInfo (EnvInfoArg field i) = show field ++ " = " ++ pprintInfo i

pprintAllocArg :: EnvAllocValueArg -> String
pprintAllocArg (EnvValueArg field x) = show field ++ " = " ++ show x

pprintSort :: Sort -> String
pprintSort IntegerH = "int"
pprintSort BooleanH = "bool"
pprintSort UnitH = "unit"
pprintSort SumH = "sum"
pprintSort StringH = "string"
pprintSort (ListH t) = "list " ++ pprintSort t
pprintSort (ProductH t s) = "pair " ++ pprintSort t ++ " " ++ pprintSort s
pprintSort (ClosureH tele) = "closure(" ++ pprintTele tele ++ ")"
pprintSort (AllocH aa) = show aa

pprintInfo :: Info -> String
pprintInfo (LocalInfo aa) = '$' : show aa
pprintInfo (EnvInfo aa) = "$." ++ show aa
pprintInfo Int64Info = "$int64"
pprintInfo BoolInfo = "$bool"
pprintInfo UnitInfo = "$unit"
pprintInfo SumInfo = "$sum"
pprintInfo StringInfo = "$string"
pprintInfo ProductInfo = "$pair"
pprintInfo ClosureInfo = "$closure"
pprintInfo ListInfo = "$list"

pprintTele :: ClosureTele -> String
pprintTele (ClosureTele ss) = intercalate ", " (map f ss)
  where
    f (ValueTele s) = pprintSort s
    f (TypeTele aa) = "forall " ++ show aa
