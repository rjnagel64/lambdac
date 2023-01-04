
module Emit
    ( emitProgram
    ) where

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
type ClosureSig = Map CodeLabel ThunkType
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

namesForClosure :: CodeLabel -> ClosureNames
namesForClosure (CodeLabel f) =
  ClosureNames {
    closureEnvName = namesForEnv (CodeLabel f)
  , closureCodeName = f ++ "_code"
  , closureEnterName = "enter_" ++ f
  }

namesForEnv :: CodeLabel -> EnvNames
namesForEnv (CodeLabel f) =
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


data ThunkArg
  = ThunkValueArg Sort
  | ThunkInfoArg
instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode

-- | Construct a thunk type from a closure telescope.
teleThunkType :: ClosureTele -> ThunkType
teleThunkType (ClosureTele ss) = ThunkType (map f ss)
  where
    f (ValueTele s) = ThunkValueArg s
    f (TypeTele aa k) = ThunkInfoArg -- Hmm. type args aren't really info args, though.

thunkTypeCode :: ThunkType -> String
thunkTypeCode (ThunkType ts) = map argcode ts
  where
    argcode ThunkInfoArg = 'I'
    argcode (ThunkValueArg s) = tycode' s
    tycode' :: Sort -> Char
    tycode' IntegerH = 'V'
    tycode' BooleanH = 'B'
    tycode' StringH = 'T'
    tycode' UnitH = 'U'
    -- In C, polymorphic types are represented uniformly.
    -- For example, 'list int64' and 'list (aa * bool)' are both represented
    -- using a 'struct list_val *' value. Therefore, when encoding a thunk type
    -- (that is, summarizing a closure's calling convention), we only need to
    -- mention the outermost constructor.
    tycode' (ClosureH _) = 'C'
    tycode' (AllocH _) = 'A'
    tycode' (ListH _) = 'L'
    tycode' (ProductH _ _) = 'Q'
    tycode' (SumH _ _) = 'S'

data ThunkNames
  = ThunkNames {
    thunkTypeName :: String
  , thunkArgsName :: String
  , thunkTraceName :: String
  , thunkSuspendName :: String
  }

namesForThunk :: ThunkType -> ThunkNames
namesForThunk ty =
  ThunkNames {
    thunkTypeName = "thunk_" ++ code
  , thunkArgsName = "args_" ++ code
  , thunkTraceName = "trace_args_" ++ code
  , thunkSuspendName = "suspend_" ++ code
  }
  where
    code = thunkTypeCode ty


typeForSort :: Sort -> String
typeForSort (AllocH _) = "struct alloc_header *"
typeForSort (ClosureH _) = "struct closure *"
typeForSort IntegerH = "struct int64_value *"
typeForSort StringH = "struct string_value *"
typeForSort BooleanH = "struct bool_value *"
typeForSort (ProductH _ _) = "struct pair *"
typeForSort (SumH _ _) = "struct sum *"
typeForSort UnitH = "struct unit *"
typeForSort (ListH _) = "struct list *"

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort IntegerH x = "AS_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "AS_CLOSURE(" ++ x ++ ")"
asSort StringH x = "AS_STRING(" ++ x ++ ")"
asSort BooleanH x = "AS_BOOL(" ++ x ++ ")"
asSort (ProductH _ _) x = "AS_PAIR(" ++ x ++ ")"
asSort (SumH _ _) x = "AS_SUM(" ++ x ++ ")"
asSort UnitH x = "AS_UNIT(" ++ x ++ ")"
asSort (ListH _s) x = "AS_LIST(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"


-- | Compute the thunk type of a closure declaration.
codeDeclType :: CodeDecl -> ThunkType
codeDeclType decl = teleThunkType (codeDeclTele decl)

-- TODO: collectThunkTypes overapproximates the set of thunk types needed by a program.
-- This bloats the output substantially as program complexity increases.
-- Instead, I should only record the thunk types I actually use.
--
-- (I believe this means traversing the program and counting each OpenH construct)
collectThunkTypes :: [CodeDecl] -> Set ThunkType
collectThunkTypes cs = foldMap closureThunkTypes cs
  where
    closureThunkTypes :: CodeDecl -> Set ThunkType
    closureThunkTypes cd@(CodeDecl _ _ params _) = Set.insert ty (foldMap paramThunkTypes params)
      where ty = codeDeclType cd

    paramThunkTypes :: ClosureParam -> Set ThunkType
    paramThunkTypes (TypeParam _ _) = Set.empty
    paramThunkTypes (PlaceParam p) = thunkTypesOf (placeSort p)

    thunkTypesOf :: Sort -> Set ThunkType
    thunkTypesOf (AllocH _) = Set.empty
    thunkTypesOf IntegerH = Set.empty
    thunkTypesOf BooleanH = Set.empty
    thunkTypesOf StringH = Set.empty
    thunkTypesOf UnitH = Set.empty
    thunkTypesOf (ClosureH tele) = Set.insert (teleThunkType tele) (teleThunkTypes tele)
    thunkTypesOf (ProductH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (SumH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (ListH t) = thunkTypesOf t

    teleThunkTypes :: ClosureTele -> Set ThunkType
    -- We are looking for thunk types, so scoping doesn't matter and foldMap is
    -- fine.
    teleThunkTypes (ClosureTele ss) = foldMap entryThunkTypes ss

    entryThunkTypes :: TeleEntry -> Set ThunkType
    entryThunkTypes (ValueTele s) = thunkTypesOf s
    entryThunkTypes (TypeTele aa k) = Set.empty



emitProgram :: Program -> [Line]
emitProgram (Program cs e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap (emitClosureDecl closureSig) cs ++
  emitEntryPoint closureSig e
  where
    closureSig = Map.fromList [(codeDeclName cd, codeDeclType cd) | cd <- cs]
    ts = Set.toList $ collectThunkTypes cs

prologue :: [Line]
prologue = ["#include \"rts.h\""]

emitEntryPoint :: ClosureSig -> TermH -> [Line]
emitEntryPoint csig e =
  ["void program_entry(void) {"] ++
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
  emitThunkArgs ns t ++
  emitThunkTrace ns t ++
  emitThunkSuspend ns t
  where ns = namesForThunk t

foldThunk :: (Int -> Sort -> b -> b) -> b -> ThunkType -> b
foldThunk consValue nil ty = go 0 (thunkArgs ty)
  where
    go _ [] = nil
    go i (ThunkValueArg s : ss) = consValue i s (go (i+1) ss)
    go i (ThunkInfoArg : ss) = go i ss

emitThunkArgs :: ThunkNames -> ThunkType -> [Line]
emitThunkArgs ns ty =
  ["struct " ++ thunkArgsName ns ++ " {"
  ,"    struct closure *closure;"] ++
  declareFields ty ++
  ["};"]
  where
    declareFields = foldThunk consValue []
      where
        consValue i s acc =
          let p = Place s (Id ("arg" ++ show i)) in
          ("    " ++ emitPlace p ++ ";") : acc

emitThunkTrace :: ThunkNames -> ThunkType -> [Line]
emitThunkTrace ns ty =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    mark_gray(AS_ALLOC(args->closure));"] ++
  body ++
  ["}"]
  where
    argsTy = "struct " ++ thunkArgsName ns ++ " *"
    body = foldThunk consValue [] ty
      where consValue i s acc = ("    mark_gray(" ++ asAlloc ("args->arg" ++ show i) ++ ");") : acc

emitThunkSuspend :: ThunkNames -> ThunkType -> [Line]
emitThunkSuspend ns ty =
  ["void " ++ thunkSuspendName ns ++ "(" ++ commaSep paramList ++ ") {"
  ,"    reserve_args(sizeof(struct " ++ thunkArgsName ns ++ "));"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    args->closure = closure;"]++
  assignFields ty ++
  ["    set_next(closure->enter, " ++ thunkTraceName ns ++ ");"
  ,"}"]
  where
    argsTy = "struct " ++ thunkArgsName ns ++ " *"
    paramList = "struct closure *closure" : foldThunk consValue [] ty
      where
        consValue i s@(AllocH _) acc =
          let p = Place s (Id ("arg" ++ show i)) in
          emitPlace p :
          acc
        consValue i s acc = let p = Place s (Id ("arg" ++ show i)) in emitPlace p : acc
    assignFields = foldThunk consValue []
      where
        consValue i _ acc =
          let arg = "arg" ++ show i in
          ("    args->" ++ arg ++ " = " ++ arg ++ ";") : acc

emitClosureDecl :: ClosureSig -> CodeDecl -> [Line]
emitClosureDecl csig cd@(CodeDecl d (envName, envd@(EnvDecl _ places)) params e) =
  emitClosureEnv cns envd ++
  emitClosureCode csig thunkEnv cns envName params e ++
  emitClosureEnter tns cns ty
  where
    cns = namesForClosure d
    tns = namesForThunk ty
    ty = codeDeclType cd

    -- The thunkEnv maps variables to their thunk type, so that the correct
    -- suspend method can be picked in emitSuspend
    thunkEnv = (foldr addParam Map.empty params, foldr addPlace Map.empty places)
    addParam (PlaceParam (Place (ClosureH tele) x)) acc = Map.insert x (teleThunkType tele) acc
    addParam (PlaceParam _) acc = acc
    addParam (TypeParam _ _) acc = acc

    addPlace (Place (ClosureH tele) x) acc = Map.insert x (teleThunkType tele) acc
    addPlace (Place _ _) acc = acc

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
  map mkField fs ++
  ["};"]
  where
    mkField f = "    " ++ emitPlace f ++ ";"

emitEnvAlloc :: EnvNames -> EnvDecl -> [Line]
emitEnvAlloc ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " *" ++ envAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ envTypeName ns ++ " *_env = malloc(sizeof(struct " ++ envTypeName ns ++ "));"]++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(_env), &" ++ envInfoName ns ++ ");"
  ,"    return _env;"
  ,"}"]
  where
    paramList = if null params then "void" else commaSep params
    params = map emitPlace fs
    assignField (Place _ x) = "    _env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: EnvNames -> EnvDecl -> [Line]
emitEnvInfo ns (EnvDecl is fs) =
  ["void " ++ envTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ show envName ++ " = (" ++ envTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"const type_info " ++ envInfoName ns ++ " = { " ++ envTraceName ns ++ ", display_env };"]
  where
    envName = Id "env"
    envTy = "struct " ++ envTypeName ns ++ " *"
    traceField (Place s x) =
      let field = asAlloc (emitName envName (EnvName x)) in
      "    mark_gray(" ++ field ++ ");"

emitClosureEnter :: ThunkNames -> ClosureNames -> ThunkType -> [Line]
emitClosureEnter tns cns ty =
  ["void " ++ closureEnterName cns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    " ++ envTy ++ "env = (" ++ envTy ++ ")args->closure->env;"
  ,"    " ++ closureCodeName cns ++ "(" ++ commaSep argList ++ ");"
  ,"}"]
  where
    argsTy = "struct " ++ thunkArgsName tns ++ " *"
    envTy = "struct " ++ envTypeName (closureEnvName cns) ++ " *"
    argList = "env" : foldThunk consValue [] ty
      where consValue i s acc = ("args->arg" ++ show i) : acc

-- Hmm. emitEntryPoint and emitClosureCode are nearly identical, save for the
-- environment pointer.
emitClosureCode :: ClosureSig -> ThunkEnv -> ClosureNames -> Id -> [ClosureParam] -> TermH -> [Line]
emitClosureCode csig tenv ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"] ++
  emitClosureBody csig tenv envName e ++
  ["}"]
  where
    paramList = commaSep (envParam : mapMaybe emitParam xs)
    envParam = "struct " ++ envTypeName (closureEnvName ns) ++ " *" ++ show envName
    emitParam (TypeParam aa k) = Nothing
    emitParam (PlaceParam p) = Just (emitPlace p)


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
emitClosureBody _ _ envp (HaltH s x) =
  ["    halt_with(" ++ asAlloc (emitName envp x) ++ ");"]
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
    args = emitName envp cl : mapMaybe makeArg (zip (thunkArgs ty) xs)

    makeArg (ThunkInfoArg, TypeArg i) = Nothing
    makeArg (ThunkValueArg _, ValueArg y) = Just (emitName envp y)
    makeArg _ = error "calling convention mismatch: type/value param paired with value/type arg"

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
        ctor = ctorCast ++ "(" ++ emitName envp x ++ ")"
        args = emitName envp k : map mkArg argNames
        mkArg (argName, Nothing) = ctor ++ "->" ++ argName
        mkArg (argName, Just argSort) = asSort argSort (ctor ++ "->" ++ argName)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

data BranchInfo
  -- How to downcast to the constructor, what thunk type to suspend with, the
  -- name of each argument, and for each argument, an (optional) sort to cast to.
  = BranchInfo String ThunkType [(String, Maybe Sort)]

-- Note: Only constructor arguments that are polymorphic need to have a cast
-- applied.
--
-- In other words, when scrutinizing 'cons @int z zs : list int', 'z' is stored
-- as a 'struct alloc_header *' and 'zs' is stored as a 'struct list *'. The
-- continuation expects 'struct int64_value *' and 'struct list *'.
--
-- Therefore, we must cast 'AS_INT64(ctor->head)' but can leave 'ctor->tail' as
-- is when suspending.
--
-- More generally, if a data type's constructor has a field of sort 'AllocH
-- aa', then that field should be cast to 't', where the case kind specifies
-- that '[aa := t]'
caseInfoTable :: CaseKind -> [BranchInfo]
caseInfoTable CaseBool =
  [ BranchInfo "AS_BOOL_FALSE" (ThunkType []) []
  , BranchInfo "AS_BOOL_TRUE" (ThunkType []) []
  ]
caseInfoTable (CaseSum t s) =
  [ BranchInfo "AS_SUM_INL" (ThunkType [ThunkValueArg t]) [("payload", Just t)]
  , BranchInfo "AS_SUM_INR" (ThunkType [ThunkValueArg s]) [("payload", Just s)]
  ]
caseInfoTable (CaseList t) =
  [ BranchInfo "AS_LIST_NIL" (ThunkType []) []
  , BranchInfo "AS_LIST_CONS" consThunkTy [("head", Just t), ("tail", Nothing)]
  ]
  where consThunkTy = ThunkType [ThunkValueArg t, ThunkValueArg (ListH t)]

emitValueAlloc :: EnvPtr -> ValueH -> String
emitValueAlloc _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc envp (BoolH True) = emitBuiltinCall envp (Id "allocate_true") []
emitValueAlloc envp (BoolH False) = emitBuiltinCall envp (Id "allocate_false") []
emitValueAlloc envp (PairH x y) =
  "allocate_pair(" ++ asAlloc (emitName envp x) ++ ", " ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ NilH = "allocate_unit()"
emitValueAlloc envp (InlH y) =
  "allocate_inl(" ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc envp (InrH y) =
  "allocate_inr(" ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ ListNilH = "allocate_list_nil()"
emitValueAlloc envp (ListConsH x xs) =
  "allocate_list_cons(" ++ asAlloc (emitName envp x) ++ ", " ++ emitName envp xs ++ ")"
emitValueAlloc _ (StringValH s) = "allocate_string(" ++ show s ++ ")"

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
emitPrimOp envp (PrimConcatenate x y) = emitPrimCall envp "prim_concatenate" [x, y]
emitPrimOp envp (PrimStrlen x) = emitPrimCall envp "prim_strlen" [x]

emitPrimCall :: EnvPtr -> String -> [Name] -> String
emitPrimCall envp fn xs = emitBuiltinCall envp (Id fn) xs

-- Hmm. I can't quite use this for emitValueAlloc, because I cannot specify
-- primitives like unboxed integers or c string literals.
--
-- I also can't use this for emitValueAlloc because if the sort of a parameter
-- is 'AllocH', I need to cast the argument with AS_ALLOC.
emitBuiltinCall :: EnvPtr -> Id -> [Name] -> String
emitBuiltinCall envp fn args = show fn ++ "(" ++ commaSep (map (emitName envp) args) ++ ")"

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
  map (allocEnv recNames envp) closures ++
  map allocClosure closures ++
  concatMap (patchEnv recNames) closures
  where recNames = Set.fromList [placeName p | ClosureAlloc p _ _ _ <- closures]

extendThunkEnv :: ClosureSig -> ThunkEnv -> [ClosureAlloc] -> ThunkEnv
extendThunkEnv csig (localThunkTys, envThunkTys) closures =
  (foldr (uncurry Map.insert) localThunkTys cs'', envThunkTys)
  where
    cs' :: [(Id, CodeLabel)]
    cs' = [(placeName (closurePlace c), closureDecl c) | c <- closures]
    cs'' :: [(Id, ThunkType)]
    cs'' = map f cs'
    f (x, d) = case Map.lookup d csig of
      Nothing -> error ("thunk type of closure " ++ show d ++ " is missing")
      Just ty -> (x, ty)

allocEnv :: Set Id -> EnvPtr -> ClosureAlloc -> Line
allocEnv recNames envp (ClosureAlloc _p d envPlace (EnvAlloc fields)) =
  "    struct " ++ envTypeName ns' ++ " *" ++ show envPlace ++ " = " ++ call ++ ";"
  where
    ns' = closureEnvName (namesForClosure d)

    call = envAllocName ns' ++ "(" ++ commaSep args ++ ")"
    args = map emitAllocArg fields
    emitAllocArg (EnvValueArg f x) = if Set.member f recNames then "NULL" else emitName envp x

allocClosure :: ClosureAlloc -> Line
allocClosure (ClosureAlloc p d envPlace _env) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep [envArg, enterArg] ++ ");"
  where
    ns = namesForClosure d
    envArg = asAlloc (show envPlace)
    enterArg = closureEnterName ns

patchEnv :: Set Id -> ClosureAlloc -> [Line]
patchEnv recNames (ClosureAlloc _ _ envPlace (EnvAlloc fields)) = concatMap patchField fields
  where
    patchField (EnvValueArg f (LocalName x)) =
      if Set.member f recNames then
        ["    " ++ show envPlace ++ "->" ++ show f ++ " = " ++ show x ++ ";"]
      else
        []
    -- Patching recursive closures should only ever involve local names.
    -- Additionally, we do not have access to an environment pointer in this function.
    patchField (EnvValueArg _ (EnvName _)) = []

emitPlace :: Place -> String
emitPlace (Place s x) = typeForSort s ++ show x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = show x
emitName envp (EnvName x) = show envp ++ "->" ++ show x

