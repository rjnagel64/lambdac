
module Emit (emitProgram) where

import Data.Function (on)
import Data.List (intercalate)
import Data.Maybe (mapMaybe)

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Hoist.IR

-- TODO: Something smarter than string and list concatenation.
-- builders? text? environment?
-- Reader EmitEnv T.Builder -- no monoid instance
-- EmitEnv -> T.Builder -- monoid instance

-- newtype Emit = Emit { runEmit :: EmitEnv -> T.Builder }
-- deriving newtype instance Semigroup Emit
-- deriving newtype instance Monoid Emit
-- Include map from name to thunk types, so OpenH and CaseH don't duplicate
-- their sort information
-- data EmitEnv = EmitEnv { envPointerName :: String, indentLevel :: Int }
-- line :: Emit -> Emit
-- line s = Emit $ \env -> B.fromText (T.replicate (indentLevel env) ' ') <> s <> B.singleton '\n'
-- text :: String -> Emit
-- text s = Emit $ \_ -> B.fromText (T.pack s)

commaSep :: [String] -> String
commaSep = intercalate ", "

type EnvPtr = Id
type Line = String

-- Associate each closure with its calling convention
type ClosureSig = Map ClosureName ThunkType
-- Associate closures in the local environment with their calling conventions.
-- (Split into two parts, because of local declarations vs. declarations from
-- the closure env)
type ThunkEnv = (Map Id ThunkType, Map Id ThunkType)

data ClosureNames
  = ClosureNames {
    closureEnvName :: EnvNames
  , closureCodeName :: String
  , closureEnterName :: String
  }

data EnvNames
  = EnvNames {
    envTypeName :: String
  , envInfoName :: String
  , envAllocName :: String
  , envTraceName :: String
  }

namesForClosure :: ClosureName -> ClosureNames
namesForClosure (ClosureName f) =
  ClosureNames {
    closureEnvName = namesForEnv (ClosureName f)
  , closureCodeName = f ++ "_code"
  , closureEnterName = "enter_" ++ f
  }

namesForEnv :: ClosureName -> EnvNames
namesForEnv (ClosureName f) =
  EnvNames {
    envTypeName = f ++ "_env"
  , envInfoName = f ++ "_env_info"
  , envAllocName = "allocate_" ++ f ++ "_env"
  , envTraceName = "trace_" ++ f ++ "_env"
  }


-- | A thunk type is a calling convention for closures: the set of arguments
-- that must be provided to open it. This information is used to generate
-- trampolined tail calls.
--
-- Because 'ThunkType' is mostly concerned with the call site, it does not have
-- a binding structure. (Or does it?)
data ThunkType = ThunkType { thunkArgs :: [ThunkArg] }


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
-- Hmm. This almost replicates the ordering-modulo-alpha-conversion thing.
-- The only thing I would need to do would be to map type variables to levels,
-- which requires the thunk types to be closed.
instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode

-- | Construct a thunk type from a closure telescope.
teleThunkType :: ClosureTele -> ThunkType
teleThunkType (ClosureTele ss) = ThunkType (map f ss)
  where
    f (ValueTele s) = ThunkValueArg s
    f (TypeTele aa) = ThunkInfoArg -- Hmm. type args aren't really info args, though.

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

data ThunkNames
  = ThunkNames {
    thunkTypeName :: String
  , thunkTraceName :: String
  , thunkSuspendName :: String
  }

namesForThunk :: ThunkType -> ThunkNames
namesForThunk ty =
  ThunkNames {
    thunkTypeName = "thunk_" ++ code
  , thunkTraceName = "trace_" ++ code
  , thunkSuspendName = "suspend_" ++ code
  }
  where
    code = thunkTypeCode ty


typeForSort :: Sort -> String
typeForSort (AllocH _) = "struct alloc_header *"
typeForSort (ClosureH _) = "struct closure *"
typeForSort IntegerH = "struct int64_value *"
typeForSort SumH = "struct sum *"
typeForSort BooleanH = "struct bool_value *"
typeForSort (ProductH _ _) = "struct pair *"
typeForSort UnitH = "struct unit *"
typeForSort (ListH _) = "struct list *"

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort IntegerH x = "AS_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "AS_CLOSURE(" ++ x ++ ")"
asSort SumH x = "AS_SUM(" ++ x ++ ")"
asSort BooleanH x = "AS_BOOL(" ++ x ++ ")"
asSort (ProductH _ _) x = "AS_PAIR(" ++ x ++ ")"
asSort UnitH x = "AS_UNIT(" ++ x ++ ")"
asSort (ListH _s) x = "AS_LIST(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"


-- | Compute the thunk type of a closure declaration.
--
-- In theory, this should just be computing the closure's telescope, then using
-- 'teleThunkType', but 'ClosureParam' and 'TeleEntry' disagree about type
-- variables versus info variables and it's a mess.
closureDeclType :: ClosureDecl -> ThunkType
closureDeclType (ClosureDecl _ _ params _) = ThunkType (map f params)
  where
    f (PlaceParam p) = ThunkValueArg (placeSort p)
    f (TypeParam i) = ThunkInfoArg

collectThunkTypes :: [ClosureDecl] -> Set ThunkType
collectThunkTypes cs = foldMap closureThunkTypes cs
  where
    closureThunkTypes :: ClosureDecl -> Set ThunkType
    closureThunkTypes cd@(ClosureDecl _ _ params _) = Set.insert ty (foldMap paramThunkTypes params)
      where ty = closureDeclType cd

    paramThunkTypes :: ClosureParam -> Set ThunkType
    paramThunkTypes (TypeParam _) = Set.empty
    paramThunkTypes (PlaceParam p) = thunkTypesOf (placeSort p)

    thunkTypesOf :: Sort -> Set ThunkType
    thunkTypesOf (AllocH _) = Set.empty
    thunkTypesOf IntegerH = Set.empty
    thunkTypesOf BooleanH = Set.empty
    thunkTypesOf SumH = Set.empty
    thunkTypesOf UnitH = Set.empty
    thunkTypesOf (ClosureH tele) = Set.insert (teleThunkType tele) (teleThunkTypes tele)
    thunkTypesOf (ProductH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (ListH t) = thunkTypesOf t

    teleThunkTypes :: ClosureTele -> Set ThunkType
    -- We are looking for thunk types, so scoping doesn't matter and foldMap is
    -- fine.
    teleThunkTypes (ClosureTele ss) = foldMap entryThunkTypes ss

    entryThunkTypes :: TeleEntry -> Set ThunkType
    entryThunkTypes (ValueTele s) = thunkTypesOf s
    entryThunkTypes (TypeTele aa) = Set.empty



emitProgram :: ([ClosureDecl], TermH) -> [Line]
emitProgram (cs, e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap (emitClosureDecl closureSig) cs ++
  emitEntryPoint closureSig e
  where
    closureSig = Map.fromList [(closureDeclName cd, closureDeclType cd) | cd <- cs]
    ts = Set.toList $ collectThunkTypes cs

prologue :: [Line]
prologue = ["#include \"rts.h\""]

emitEntryPoint :: ClosureSig -> TermH -> [Line]
emitEntryPoint csig e =
  ["void program_entry(void) {"] ++
  -- There is no top-level environment. All names are local.
  emitClosureBody csig thunkEnv envp e ++
  ["}"]
  where
    -- There is no environment pointer at the top level, because we are not in a closure.
    envp = Id "NULL"
    -- Likewise, there are no fields in the environment.
    -- Also, we start with no local variables.
    thunkEnv = (Map.empty, Map.empty)

emitThunkDecl :: ThunkType -> [Line]
emitThunkDecl t =
  emitThunkSuspend (namesForThunk t) t

foldThunk :: (Int -> Sort -> b -> b) -> (Int -> b -> b) -> b -> ThunkType -> b
foldThunk consValue consInfo nil ty = go 0 0 (thunkArgs ty)
  where
    go _ _ [] = nil
    go i j (ThunkValueArg s : ss) = consValue i s (go (i+1) j ss)
    go i j (ThunkInfoArg : ss) = consInfo j (go i (j+1) ss)

emitThunkSuspend :: ThunkNames -> ThunkType -> [Line]
emitThunkSuspend ns ty =
  ["void " ++ thunkSuspendName ns ++ "(" ++ commaSep paramList ++ ") {"
  ,"    next_closure = closure;"
  ,"    next_step->enter = closure->enter;"
  ,"    reserve_args(" ++ show numValues ++ ", " ++ show numInfos ++ ");"] ++
  assignFields ty ++
  ["}"]
  where
    paramList = "struct closure *closure" : foldThunk consValue consInfo [] ty
      where
        consValue i (AllocH _) acc =
          ("struct alloc_header *arg" ++ show i) : ("type_info arginfo" ++ show i) : acc
        consValue i s acc = emitPlace (Place s (Id ("arg" ++ show i))) : acc
        consInfo j acc = ("type_info info" ++ show j) : acc

    numValues, numInfos :: Int
    (numValues, numInfos) = foldThunk (\_ _ (i, j) -> (i+1, j)) (\_ (i, j) -> (i, j+1)) (0, 0) ty

    assignFields = foldThunk consValue consInfo []
      where
        consValue i s acc =
          let
            info = case s of
              AllocH _ -> LocalInfo (Id ("arginfo" ++ show i))
              IntegerH -> Int64Info
              BooleanH -> BoolInfo
              UnitH -> UnitInfo
              SumH -> SumInfo
              ProductH _ _ -> ProductInfo
              ListH _ -> ListInfo
              ClosureH _ -> ClosureInfo
          in
          let lval = "next_step->args->values[" ++ show i ++ "]" in 
          ("    " ++ lval ++ ".alloc = " ++ asAlloc ("arg" ++ show i) ++ ";") :
          ("    " ++ lval ++ ".info = " ++ emitInfo (Id "NULL") info ++ ";") :
          acc
        consInfo j acc =
          ("   next_step->args->infos[" ++ show j ++ "] = info" ++ show j ++ ";") :
          acc

emitClosureDecl :: ClosureSig -> ClosureDecl -> [Line]
emitClosureDecl csig cd@(ClosureDecl d (envName, envd@(EnvDecl _ places)) params e) =
  emitClosureEnv ns envd ++
  emitClosureCode csig thunkEnv ns envName params e ++
  emitClosureEnter ns ty
  where
    ns = namesForClosure d
    ty = closureDeclType cd

    thunkEnv = (Map.fromList $ mapMaybe f params, Map.fromList $ mapMaybe g places)
    f (TypeParam _) = Nothing
    f (PlaceParam p) = case placeSort p of
      ClosureH tele -> Just (placeName p, teleThunkType tele)
      _ -> Nothing
    g p = case placeSort p of
      ClosureH tele -> Just (placeName p, teleThunkType tele)
      _ -> Nothing

emitClosureEnv :: ClosureNames -> EnvDecl -> [Line]
emitClosureEnv ns envd =
  let ns' = closureEnvName ns in
  emitEnvDecl ns' envd ++
  emitEnvInfo ns' envd ++
  emitEnvAlloc ns' envd

emitEnvDecl :: EnvNames -> EnvDecl -> [Line]
emitEnvDecl ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkInfo is ++
  map mkField fs ++
  ["};"]
  where
    mkInfo i = "    " ++ emitInfoPlace i ++ ";"
    mkField f = "    " ++ emitPlace f ++ ";"

emitEnvAlloc :: EnvNames -> EnvDecl -> [Line]
emitEnvAlloc ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " *" ++ envAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ envTypeName ns ++ " *_env = malloc(sizeof(struct " ++ envTypeName ns ++ "));"]++
  map assignInfo is ++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(_env), " ++ envInfoName ns ++ ");"
  ,"    return _env;"
  ,"}"]
  where
    paramList = if null params then "void" else commaSep params
    params = map emitInfoPlace is ++ map emitPlace fs

    assignInfo (InfoPlace aa) = "    _env->" ++ show aa ++ " = " ++ show aa ++ ";"
    assignField (Place _ x) = "    _env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: EnvNames -> EnvDecl -> [Line]
emitEnvInfo ns (EnvDecl is fs) =
  ["void " ++ envTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ show envName ++ " = (" ++ envTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"type_info " ++ envInfoName ns ++ " = { " ++ envTraceName ns ++ ", display_env };"]
  where
    envName = Id "env"
    envTy = "struct " ++ envTypeName ns ++ " *"
    traceField (Place s x) =
      let i = infoFor s in
      "    mark_gray(" ++ asAlloc (emitName envName (EnvName x)) ++ ", " ++ emitInfo envName i ++ ");"

    -- The set of type infos available in this environment, to be used for
    -- tracing polymorphic fields.
    typeInfos :: Map TyVar Info
    typeInfos = Map.fromList $ [(TyVar aa, EnvInfo (Id aa)) | InfoPlace (Id aa) <- is]

    -- Using the type infos in the environment, determine how to trace a field of sort 's'.
    infoFor :: Sort -> Info
    infoFor (AllocH aa) = case Map.lookup aa typeInfos of
      Nothing -> error ("Missing info to trace polymorphic field of type " ++ show aa)
      Just i -> i
    infoFor IntegerH = Int64Info
    infoFor BooleanH = BoolInfo
    infoFor UnitH = UnitInfo
    infoFor SumH = SumInfo
    infoFor (ProductH _ _) = ProductInfo
    infoFor (ListH _) = ListInfo
    infoFor (ClosureH _) = ClosureInfo

emitClosureEnter :: ClosureNames -> ThunkType -> [Line]
emitClosureEnter ns ty =
  ["void " ++ closureEnterName ns ++ "(void) {"
  ,"    " ++ thunkTy ++ "next = (" ++ thunkTy ++ ")next_step;"
  ,"    " ++ envTy ++ "env = (" ++ envTy ++ ")next_closure->env;"
  ,"    " ++ closureCodeName ns ++ "(" ++ commaSep argList ++ ");"
  ,"}"]
  where
    thunkTy = "struct " ++ thunkTypeName (namesForThunk ty) ++ " *"
    envTy = "struct " ++ envTypeName (closureEnvName ns) ++ " *"
    argList = "env" : foldThunk consValue consInfo [] ty
      where
        consValue i s acc = asSort s ("next_step->args->values[" ++ show i ++ "].alloc") : acc
        consInfo j acc = ("next_step->args->infos[" ++ show j ++ "]") : acc

-- Hmm. emitEntryPoint and emitClosureCode are nearly identical, save for the
-- environment pointer.
emitClosureCode :: ClosureSig -> ThunkEnv -> ClosureNames -> Id -> [ClosureParam] -> TermH -> [Line]
emitClosureCode csig tenv ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"] ++
  emitClosureBody csig tenv envName e ++
  ["}"]
  where
    paramList = commaSep (envParam : map emitParam xs)
    envParam = "struct " ++ envTypeName (closureEnvName ns) ++ " *" ++ show envName
    emitParam (TypeParam i) = emitInfoPlace i
    emitParam (PlaceParam p) = emitPlace p


emitClosureBody :: ClosureSig -> ThunkEnv -> EnvPtr -> TermH -> [Line]
emitClosureBody csig tenv envp (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValueAlloc envp v ++ ";"] ++
  emitClosureBody csig tenv envp e
emitClosureBody csig tenv envp (LetProjectH x y ProjectFst e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->fst") ++ ";"] ++
  emitClosureBody csig tenv envp e
emitClosureBody csig tenv envp (LetProjectH x y ProjectSnd e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->snd") ++ ";"] ++
  emitClosureBody csig tenv envp e
emitClosureBody csig tenv envp (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp envp p ++ ";"] ++
  emitClosureBody csig tenv envp e
emitClosureBody csig tenv envp (AllocClosure cs e) =
  emitClosureGroup envp cs ++
  let tenv' = extendThunkEnv csig tenv cs in
  emitClosureBody csig tenv' envp e
emitClosureBody _ _ envp (HaltH _s x i) =
  ["    halt_with(" ++ asAlloc (emitName envp x) ++ ", " ++ emitInfo envp i ++ ");"]
emitClosureBody _ tenv envp (OpenH c args) =
  [emitSuspend tenv envp c args]
emitClosureBody _ _ envp (CaseH x kind ks) =
  emitCase kind envp x ks

emitSuspend :: ThunkEnv -> EnvPtr -> Name -> [ClosureArg] -> Line
emitSuspend tenv envp cl xs =
  "    " ++ method ++ "(" ++ commaSep args ++ ");"
  where
    ty = lookupThunkTy tenv cl
    method = thunkSuspendName (namesForThunk ty)
    args = emitName envp cl : zipWith makeArg (thunkArgs ty) xs

    makeArg ThunkInfoArg (TypeArg i) = emitInfo envp i
    makeArg (ThunkValueArg (AllocH _)) (OpaqueArg y i) = emitName envp y ++ ", " ++ emitInfo envp i
    makeArg (ThunkValueArg _) (OpaqueArg _ _) =
      error "only 'alloc' thunk args should be passed as opaque values"
    makeArg (ThunkValueArg (AllocH _)) (ValueArg _) =
      error "'alloc' thunk args should be opaque values"
    makeArg (ThunkValueArg _) (ValueArg y) = emitName envp y
    makeArg _ _ = error "calling convention mismatch: type/value param paired with value/type arg"

lookupThunkTy :: ThunkEnv -> Name -> ThunkType
lookupThunkTy (localThunkTys, _) (LocalName x) = case Map.lookup x localThunkTys of
  Nothing -> error ("missing thunk type for name " ++ show x)
  Just ty -> ty
lookupThunkTy (_, envThunkTys) (EnvName x) = case Map.lookup x envThunkTys of
  Nothing -> error ("missing thunk type for name " ++ show x)
  Just ty -> ty


emitCase :: CaseKind -> EnvPtr -> Name -> [Name] -> [Line]
emitCase kind envp x ks =
  ["    switch (" ++ emitName envp x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch (zip3 [0..] (caseInfoTable kind) ks) ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: (Int, BranchInfo, Name) -> [String]
    emitCaseBranch (i, BranchInfo ctorCast ty argNames, k) =
      let
        method = thunkSuspendName (namesForThunk ty)
        args = emitName envp k : map mkArg argNames
        mkArg (argName, Nothing) =
          ctorCast ++ "(" ++ emitName envp x ++ ")->" ++ argName
        mkArg (argName, Just argSort) =
          asSort argSort (ctorCast ++ "(" ++ emitName envp x ++ ")->" ++ argName)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

data BranchInfo
  -- How to downcast to the constructor, what thunk type to suspend with, and
  -- the name/sort of each argument to extract.
  --
  -- argSort is 'Just t' for a value argument, or 'Nothing' for an info argument.
  = BranchInfo String ThunkType [(String, Maybe Sort)]

caseInfoTable :: CaseKind -> [BranchInfo]
caseInfoTable CaseBool =
  [ BranchInfo "AS_BOOL_FALSE" (ThunkType []) []
  , BranchInfo "AS_BOOL_TRUE" (ThunkType []) []
  ]
caseInfoTable (CaseSum t s) =
  -- If the field is polymorphic, we need to pass extra info arguments to the
  -- suspend method.
  let
    makeArg name info sort@(AllocH _) = [(name, Just sort), (info, Nothing)]
    makeArg name _ sort = [(name, Just sort)]
  in
  [ BranchInfo "AS_SUM_INL" (ThunkType [ThunkValueArg t]) (makeArg "payload" "info" t)
  , BranchInfo "AS_SUM_INR" (ThunkType [ThunkValueArg s]) (makeArg "payload" "info" s)
  ]
caseInfoTable (CaseList t) =
  let
    makeArg name info sort@(AllocH _) = [(name, Just sort), (info, Nothing)]
    makeArg name _ sort = [(name, Just sort)]
  in
  [ BranchInfo "AS_LIST_NIL" (ThunkType []) []
  , BranchInfo "AS_LIST_CONS" consThunkTy (makeArg "head" "head_info" t ++ makeArg "tail" "" (ListH t))
  ]
  where consThunkTy = ThunkType [ThunkValueArg t, ThunkValueArg (ListH t)]

emitValueAlloc :: EnvPtr -> ValueH -> String
emitValueAlloc _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc _ (BoolH True) = "allocate_true()"
emitValueAlloc _ (BoolH False) = "allocate_false()"
emitValueAlloc envp (PairH s1 s2 x y) =
  "allocate_pair(" ++ emitInfo envp s1 ++ ", " ++ emitInfo envp s2 ++ ", " ++ asAlloc (emitName envp x) ++ ", " ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ NilH = "allocate_unit()"
emitValueAlloc envp (InlH s y) =
  "allocate_inl(" ++ asAlloc (emitName envp y) ++ ", " ++ emitInfo envp s ++ ")"
emitValueAlloc envp (InrH s y) =
  "allocate_inr(" ++ asAlloc (emitName envp y) ++ ", " ++ emitInfo envp s ++ ")"
emitValueAlloc _ ListNilH = "allocate_list_nil()"
emitValueAlloc envp (ListConsH s x xs) =
  "allocate_list_cons(" ++ asAlloc (emitName envp x) ++ ", " ++ emitInfo envp s ++ ", " ++ emitName envp xs ++ ")"

emitPrimOp :: EnvPtr -> PrimOp -> String
emitPrimOp envp (PrimAddInt64 x y) = emitPrimCall envp "prim_addint64" [x, y]
emitPrimOp envp (PrimSubInt64 x y) = emitPrimCall envp "prim_subint64" [x, y]
emitPrimOp envp (PrimMulInt64 x y) = emitPrimCall envp "prim_mulint64" [x, y]
emitPrimOp envp (PrimNegInt64 x) = emitPrimCall envp "prim_negint64" [x]
emitPrimOp envp (PrimEqInt64 x y) = emitPrimCall envp "prim_eqint64" [x, y]
emitPrimOp envp (PrimNeInt64 x y) = emitPrimCall envp "prim_neint64" [x, y]
emitPrimOp envp (PrimLtInt64 x y) = emitPrimCall envp "prim_ltint64" [x, y]
emitPrimOp envp (PrimLeInt64 x y) = emitPrimCall envp "prim_leint64" [x, y]
emitPrimOp envp (PrimGtInt64 x y) = emitPrimCall envp "prim_gtint64" [x, y]
emitPrimOp envp (PrimGeInt64 x y) = emitPrimCall envp "prim_geint64" [x, y]

-- TODO: emitPrimCall could take a list of type/info arguments?
emitPrimCall :: EnvPtr -> String -> [Name] -> String
emitPrimCall envp fn xs = fn ++ "(" ++ commaSep (map (emitName envp) xs) ++ ")"

-- | Allocate a group of (mutually recursive) closures.
--
-- This is a three-step process.
-- - First, each closure's environment is allocated. Cyclic references are
--   initialized with @NULL@.
-- - Second, the closures are allocated using the environments from step 1.
-- - Third, the @NULL@s in the environments are patched to refer to the
--   freshly-allocated closures.
emitClosureGroup :: EnvPtr -> [ClosureAlloc] -> [Line]
emitClosureGroup envp closures =
  map (allocEnv envp) closures ++
  map allocClosure closures ++
  concatMap patchEnv closures

extendThunkEnv :: ClosureSig -> ThunkEnv -> [ClosureAlloc] -> ThunkEnv
extendThunkEnv csig (localThunkTys, envThunkTys) closures =
  (foldr (uncurry Map.insert) localThunkTys cs'', envThunkTys)
  where
    cs' :: [(Id, ClosureName)]
    cs' = [(placeName (closurePlace c), closureDecl c) | c <- closures]
    cs'' :: [(Id, ThunkType)]
    cs'' = map f cs'
    f (x, d) = case Map.lookup d csig of
      Nothing -> error ("thunk type of closure " ++ show d ++ " is missing")
      Just ty -> (x, ty)

allocEnv :: EnvPtr -> ClosureAlloc -> Line
allocEnv envp (ClosureAlloc _p d envPlace (EnvAlloc info fields)) =
  "    struct " ++ envTypeName ns' ++ " *" ++ show envPlace ++ " = " ++ call ++ ";"
  where
    ns' = closureEnvName (namesForClosure d)

    call = envAllocName ns' ++ "(" ++ commaSep args ++ ")"
    args = map (emitInfo envp . snd) info ++ map emitAllocArg fields
    emitAllocArg (EnvFreeArg _ x) = emitName envp x
    emitAllocArg (EnvRecArg _ _) = "NULL"

allocClosure :: ClosureAlloc -> Line
allocClosure (ClosureAlloc p d envPlace _env) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep args ++ ");"
  where
    ns = namesForClosure d
    ns' = closureEnvName ns
    args = [envArg, traceArg, enterArg]
    envArg = asAlloc (show envPlace)
    traceArg = envInfoName ns'
    enterArg = closureEnterName ns

patchEnv :: ClosureAlloc -> [Line]
patchEnv (ClosureAlloc _ _ envPlace (EnvAlloc _info fields)) = concatMap patchField fields
  where
    patchField (EnvFreeArg _ _) = []
    patchField (EnvRecArg (Place _ f) (LocalName x)) =
      ["    " ++ show envPlace ++ "->" ++ show f ++ " = " ++ show x ++ ";"]
    -- Patching recursive closures should only ever involve local names.
    -- Additionally, we do not have access to an environment pointer in this function.
    patchField (EnvRecArg _ (EnvName _)) = []

emitInfoPlace :: InfoPlace -> String
emitInfoPlace (InfoPlace i) = "type_info " ++ show i

emitPlace :: Place -> String
emitPlace (Place s x) = typeForSort s ++ show x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = show x
emitName envp (EnvName x) = show envp ++ "->" ++ show x

emitInfo :: EnvPtr -> Info -> String
emitInfo _ (LocalInfo aa) = show aa
emitInfo envp (EnvInfo aa) = show envp ++ "->" ++ show aa
emitInfo _ Int64Info = "int64_value_info"
emitInfo _ BoolInfo = "bool_value_info"
emitInfo _ UnitInfo = "unit_info"
emitInfo _ SumInfo = "sum_info"
emitInfo _ ProductInfo = "pair_info"
emitInfo _ ClosureInfo = "closure_info"
emitInfo _ ListInfo = "list_info"

