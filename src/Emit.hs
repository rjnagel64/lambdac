
module Emit (emitProgram) where

import Data.List (intercalate)

import qualified Hoist as H
import Hoist

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

type EnvPtr = String

emitProgram :: ([ThunkType], [ClosureDecl], TermH) -> [String]
emitProgram (ts, cs, e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap emitClosureDecl cs ++
  emitEntryPoint e

data ClosureNames
  = ClosureNames {
    closureEnvName :: String
  , closureEnvInfo :: String
  , closureAllocName :: String
  , closureTraceName :: String
  , closureCodeName :: String
  }

namesForDecl :: DeclName -> ClosureNames
namesForDecl (DeclName f) =
  ClosureNames {
    -- These methods (except closureCodeName) are very similar to declaring a
    -- product type, though the trace method is not a proper type info.
    -- (The env is not an alloc_header, and the trace method is not wrapped in
    -- a 'type_info')
    closureEnvName = f ++ "_env"
  , closureEnvInfo = f ++ "_env_info"
  , closureAllocName = "allocate_" ++ f ++ "_env"
  , closureTraceName = "trace_" ++ f ++ "_env"
  , closureCodeName = f ++ "_code"
  }

prologue :: [String]
prologue = ["#include \"rts.h\""]

emitEntryPoint :: TermH -> [String]
emitEntryPoint e =
  ["void program_entry(void) {"] ++
  emitClosureBody "NULL" e ++ -- There is no top-level environment. All names are local.
  ["}"]

data ThunkNames
  = ThunkNames {
    thunkTypeName :: String
  , thunkEnterName :: String
  , thunkTraceName :: String
  , thunkSuspendName :: String
  }


namesForThunk :: ThunkType -> ThunkNames
namesForThunk ty =
  ThunkNames {
    thunkTypeName = "thunk_" ++ code
  , thunkEnterName = "enter_" ++ code
  , thunkTraceName = "trace_" ++ code
  , thunkSuspendName = "suspend_" ++ code
  }
  where
    code = thunkTypeCode ty

typeForSort :: Sort -> String
typeForSort (AllocH aa) = "struct alloc_header *"
typeForSort (InfoH aa) = "type_info "
typeForSort (ClosureH _) = "struct closure *"
typeForSort IntegerH = "struct int64_value *"
typeForSort SumH = "struct sum *"
typeForSort BooleanH = "struct bool_value *"
typeForSort (ProductH _ _) = "struct pair *"
typeForSort UnitH = "struct unit *"
typeForSort (ListH _) = "struct list *"

infoForSort :: EnvPtr -> Sort -> String
infoForSort _ (InfoH aa) = error "Info for type_info shouldn't be necessary? (unless it is?)"
infoForSort envp (AllocH aa) = envp ++ "->" ++ show aa
infoForSort _ SumH = "sum_info"
infoForSort _ BooleanH = "bool_value_info"
infoForSort _ IntegerH = "int64_value_info"
infoForSort _ (ProductH _ _) = "pair_info"
infoForSort _ UnitH = "unit_info"
infoForSort _ (ClosureH _) = "closure_info"
infoForSort _ (ListH _) = "list_info"

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort (InfoH _) x = error "we should not be casting to/from type_info"
asSort IntegerH x = "AS_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "AS_CLOSURE(" ++ x ++ ")"
asSort SumH x = "AS_SUM(" ++ x ++ ")"
asSort BooleanH x = "AS_BOOL(" ++ x ++ ")"
asSort (ProductH _ _) x = "AS_PAIR(" ++ x ++ ")"
asSort UnitH x = "AS_UNIT(" ++ x ++ ")"
asSort (ListH _s) x = "AS_LIST(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"

emitMarkGray :: EnvPtr -> String -> Sort -> String
emitMarkGray envp x (InfoH _) = "" -- TODO: This produces extraneous blank lines
emitMarkGray envp x s = "mark_gray(" ++ asAlloc x ++ ", " ++ infoForSort envp s ++ ")"

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0..]

-- TODO: Generate per-sort allocate_closure methods?
-- I think I need to still maintain only one 'struct closure' (because
-- pointer-casting and struct-casting issues), but I think I can make
-- allocate_closure per-sort. This would move around the function pointer casts
-- a bit, make them more encapsulated.
emitThunkDecl :: ThunkType -> [String]
emitThunkDecl t =
  emitThunkType t ++
  emitThunkEnter t ++
  emitThunkTrace t ++
  emitThunkSuspend t

emitThunkType :: ThunkType -> [String]
emitThunkType ty@(ThunkType ss) =
  ["struct " ++ thunkTypeName ns ++ " {"
  ,"    struct thunk header;"
  ,"    struct closure *closure;"] ++
  mapWithIndex mkField ss ++
  ["};"]
  where
    ns = namesForThunk ty
    mkField i (AllocH _) = "    struct alloc_header *arg" ++ show i ++ ";\n    type_info info" ++ show i ++ ";"
    mkField i s = "    " ++ emitFieldDecl (FieldName s ("arg" ++ show i)) ++ ";"
    -- TODO: `struct alloc_header` in a thunk should be accompanied by `type_info`

emitThunkTrace :: ThunkType -> [String]
emitThunkTrace ty@(ThunkType ss) =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    " ++ emitMarkGray "next" "next->closure" (ClosureH ss) ++ ";"] ++
  mapWithIndex traceField ss ++
  ["}"]
  where
    ns = namesForThunk ty
    traceField i (AllocH _) = "    mark_gray(next->arg" ++ show i ++ ", next->info" ++ show i ++ ");"
    traceField i s = "    " ++ emitMarkGray "next" ("next->arg" ++ show i) s ++ ";"

emitThunkEnter :: ThunkType -> [String]
emitThunkEnter ty@(ThunkType ss) =
  ["void " ++ thunkEnterName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    void (*code)(" ++ paramList ++ ") = (void (*)(" ++ paramList ++ "))next->closure->code;"
  ,"    code(" ++ argList ++ ");"
  ,"}"]
  where
    ns = namesForThunk ty
    paramList = commaSep ("void *env" : mapWithIndex makeParam ss)
    makeParam i s = emitPlace (PlaceName s ("arg" ++ show i))
    argList = commaSep ("next->closure->env" : mapWithIndex makeArgument ss)
    makeArgument i _ = "next->arg" ++ show i

emitThunkSuspend :: ThunkType -> [String]
emitThunkSuspend ty@(ThunkType ss) =
  ["void " ++ thunkSuspendName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = realloc(next_step, sizeof(struct " ++ thunkTypeName ns ++ "));"
  ,"    next->header.enter = closure->enter;"
  ,"    next->header.trace = " ++ thunkTraceName ns ++ ";"
  ,"    next->closure = closure;"] ++
  mapWithIndex assignField ss ++
  ["    next_step = (struct thunk *)next;"
  ,"}"]
  where
    ns = namesForThunk ty
    paramList = commaSep ("struct closure *closure" : mapWithIndex makeParam ss)
    makeParam i (AllocH _) = "struct alloc_header *arg" ++ show i ++ ", type_info info" ++ show i
    makeParam i s = emitPlace (PlaceName s ("arg" ++ show i))
    assignField i _ = "    next->arg" ++ show i ++ " = arg" ++ show i ++ ";"

emitClosureDecl :: H.ClosureDecl -> [String]
emitClosureDecl (H.ClosureDecl d (envName, envd) params e) =
  emitEnvDecl ns envd ++
  emitEnvTrace ns envd ++
  emitEnvAlloc ns envd ++
  emitClosureCode ns envName params e
  where ns = namesForDecl d

emitEnvDecl :: ClosureNames -> EnvDecl -> [String]
emitEnvDecl ns (EnvDecl is fs) =
  ["struct " ++ closureEnvName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkInfo is ++
  map mkField fs ++
  ["};"]
  where
    mkInfo i = "    " ++ emitInfoDecl i ++ ";"
    mkField f = "    " ++ emitFieldDecl f ++ ";"

emitEnvAlloc :: ClosureNames -> EnvDecl -> [String]
-- TODO: What if there is a parameter named 'env'?
emitEnvAlloc ns (EnvDecl is fs) =
  ["struct " ++ closureEnvName ns ++ " *" ++ closureAllocName ns ++ "(" ++ params ++ ") {"
  ,"    struct " ++ closureEnvName ns ++ " *env = malloc(sizeof(struct " ++ closureEnvName ns ++ "));"]++
  map assignInfo is ++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(env), " ++ closureEnvInfo ns ++ ");"
  ,"    return env;"
  ,"}"]
  where
    params = if null is && null fs then "void" else commaSep (map emitInfoDecl is ++ map emitFieldDecl fs)

    assignInfo :: InfoName -> String
    assignInfo aa = "    env->" ++ infoName aa ++ " = " ++ infoName aa ++ ";"

    assignField :: FieldName -> String
    assignField (FieldName _ x) = "    env->" ++ x ++ " = " ++ x ++ ";"

-- | Emit a method to trace a closure environment.
-- (And also emit type info for the environment types)
emitEnvTrace :: ClosureNames -> EnvDecl -> [String]
emitEnvTrace ns (EnvDecl _is fs) =
  ["void " ++ closureTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ closureTy ++ "env = (" ++ closureTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"type_info " ++ closureEnvName ns ++ "_info = { " ++ closureTraceName ns ++ ", display_env };"]
  where
    closureTy = "struct " ++ closureEnvName ns ++ " *"
    traceField :: FieldName -> String
    traceField (FieldName s x) = "    " ++ emitMarkGray "env" ("env->" ++ x) s ++ ";"

emitClosureCode :: ClosureNames -> String -> [ClosureParam] -> TermH -> [String]
emitClosureCode ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ closureEnvName ns ++ " *" ++ envName ++ " = __env;"] ++
  emitClosureBody envName e ++
  ["}"]
  where
    -- User-provided names cannot start with _, so we use that for the
    -- polymorphic environment parameter.
    paramList = commaSep ("void *__env" : map emitParam xs)
    emitParam (TypeParam i) = emitInfoDecl i
    emitParam (PlaceParam p) = emitPlace p

emitClosureBody :: EnvPtr -> TermH -> [String]
emitClosureBody envp (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValueAlloc envp v ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (LetProjectH x y ProjectFst e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->fst") ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (LetProjectH x y ProjectSnd e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->snd") ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp envp p ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (AllocClosure cs e) =
  emitAllocGroup envp cs ++
  emitClosureBody envp e
emitClosureBody envp (HaltH x s) =
  ["    halt_with(" ++ asAlloc (emitName envp x) ++ ", " ++ infoForSort envp s ++ ");"]
emitClosureBody envp (OpenH c ty xs) =
  [emitSuspend3 envp c ty xs]
emitClosureBody envp (InstH f ty ss ks) =
  [emitSuspend' envp f ty ss ks]
emitClosureBody envp (CaseH x kind ks) =
  emitCase kind envp x ks

-- TODO: Every argument of sort 'Alloc aa' becomes two arguments: 'struct alloc_header *, type_info'.
-- This is possibly redundant, if multiple arguments use the same 'type_info', but it's simpler.
emitSuspend :: EnvPtr -> Name -> ThunkType -> [Name] -> String
emitSuspend envp cl ty xs = "    " ++ emitPrimCall envp method (cl : xs) ++ ";"
  where
    method = thunkSuspendName (namesForThunk ty)

emitSuspend' :: EnvPtr -> Name -> ThunkType -> [Sort] -> [Name] -> String
emitSuspend' envp cl ty ss xs =
  "    " ++ method ++ "(" ++ emitName envp cl ++ ", " ++ commaSep (map (infoForSort envp) ss) ++ ", " ++ commaSep (map (emitName envp) xs) ++ ");"
  where
    method = thunkSuspendName (namesForThunk ty)

emitSuspend3 :: EnvPtr -> Name -> ThunkType -> [Name] -> String
emitSuspend3 envp cl ty@(ThunkType ss) xs = "    " ++ method ++ "(" ++ args ++ ");"
  where
    method = thunkSuspendName (namesForThunk ty)
    args = commaSep (emitName envp cl : mapWithIndex makeArg (zip ss xs))
    -- TODO: Emit proper info when suspending
    -- I honestly think I need an analog of LocalName/EnvName for info.
    -- Or this is more evidence that info should be folded into Name
    makeArg i (AllocH aa, x) = emitName envp x ++ ", " ++ infoForSort envp (AllocH aa)
    makeArg i (s, x) = emitName envp x

emitCase :: CaseKind -> EnvPtr -> Name -> [(Name, ThunkType)] -> [String]
emitCase kind envp x ks =
  ["    switch (" ++ emitName envp x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch (zip3 [0..] (branchArgNames kind) ks) ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: (Int, (String, [String]), (Name, ThunkType)) -> [String]
    emitCaseBranch (i, (ctorCast, argNames), (k, ty@(ThunkType ss))) =
      let
        method = thunkSuspendName (namesForThunk ty)
        args = emitName envp k : zipWith mkArg argNames ss
        mkArg argName argSort = asSort argSort (ctorCast ++ "(" ++ emitName envp x ++ ")->" ++ argName)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

    branchArgNames CaseBool = [("AS_BOOL_FALSE", []), ("AS_BOOL_TRUE", [])]
    branchArgNames CaseSum = [("AS_SUM_INL", ["payload"]), ("AS_SUM_INR", ["payload"])]
    branchArgNames CaseList = [("AS_LIST_NIL", []), ("AS_LIST_CONS", ["head", "tail"])]

emitValueAlloc :: EnvPtr -> ValueH -> String
emitValueAlloc _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc _ (BoolH True) = "allocate_true()"
emitValueAlloc _ (BoolH False) = "allocate_false()"
emitValueAlloc envp (PairH (x, s1) (y, s2)) =
  "allocate_pair(" ++ infoForSort envp s1 ++ ", " ++ infoForSort envp s2 ++ ", " ++ asAlloc (emitName envp x) ++ ", " ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ NilH = "allocate_unit()"
emitValueAlloc envp (InlH s y) =
  "allocate_inl(" ++ asAlloc (emitName envp y) ++ ", " ++ infoForSort envp s ++ ")"
emitValueAlloc envp (InrH s y) =
  "allocate_inr(" ++ asAlloc (emitName envp y) ++ ", " ++ infoForSort envp s ++ ")"
emitValueAlloc _ ListNilH = "allocate_list_nil()"
emitValueAlloc envp (ListConsH s x xs) =
  "allocate_list_cons(" ++ asAlloc (emitName envp x) ++ ", " ++ infoForSort envp s ++ ", " ++ emitName envp xs ++ ")"

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

emitAllocGroup :: EnvPtr -> [ClosureAlloc] -> [String]
emitAllocGroup envp closures =
  map (emitAlloc envp) closures ++
  concatMap (\ (ClosureAlloc p _ty d env) -> emitPatch (namesForDecl d) p env) closures

emitAlloc :: EnvPtr -> ClosureAlloc -> String
emitAlloc envp (ClosureAlloc p ty d (EnvAlloc info free rec)) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep args ++ ");"
  where
    ns = namesForDecl d
    args = [envArg, traceArg, codeArg, enterArg]
    envArg = asAlloc (closureAllocName ns ++ "(" ++ commaSep envAllocArgs ++ ")")
    traceArg = closureEnvInfo ns
    codeArg = "(void (*)(void))" ++ closureCodeName ns
    enterArg = thunkEnterName (namesForThunk ty)

    -- Recursive/cyclic environment references are initialized to NULL, and
    -- then patched once all the closures have been allocated.
    infoArgs = map (infoForSort envp . AllocH . snd) info
    envAllocArgs = infoArgs ++ map (emitName envp . snd) free ++ map (const "NULL") rec

emitPatch :: ClosureNames -> PlaceName -> EnvAlloc -> [String]
emitPatch ns (PlaceName _ p) (EnvAlloc _info _free rec) =
  concatMap patchField rec
  where
    env = "((struct " ++ closureEnvName ns ++ " *)" ++ p ++ "->env)"
    patchField (FieldName _ f, LocalName x) = ["    " ++ env ++ "->" ++ f ++ " = " ++ x ++ ";"]
    patchField (_, EnvName _) = [] -- Why ignore environment names?

emitFieldDecl :: FieldName -> String
emitFieldDecl (FieldName s x) = typeForSort s ++ x

emitInfoDecl :: InfoName -> String
emitInfoDecl (InfoName i) = "type_info " ++ i

emitPlace :: PlaceName -> String
emitPlace (PlaceName s x) = typeForSort s ++ x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = x
emitName envp (EnvName x) = envp ++ "->" ++ x

