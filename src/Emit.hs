
module Emit (emitProgram) where

import qualified Data.Set as Set
import Data.Set (Set)

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

-- TODO: Ensure declarations (esp. product type declarations) are emitted in topological order
-- TODO: Stop collecting ProductType.
emitProgram :: (Set ThunkType, [ClosureDecl], TermH) -> [String]
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

-- This scheme will almost certainly break down as types get fancier.
-- For example, polymorphic pair with distinct types vs. polymorphic pair with
-- one type for both arguments.
--
-- (e.g., (a, a) and (a, b) are both P2AA)
tycode :: Sort -> String
tycode (Closure ss) = 'C' : show (length ss) ++ concatMap tycode ss
tycode Integer = "V"
tycode (Alloc aa) = error "tycode: schema not expressive enough"
tycode Sum = "S"
tycode Boolean = "B"
tycode (Pair s t) = 'Q' : tycode s ++ tycode t
tycode Unit = "U"
tycode (List s) = 'L' : tycode s

namesForThunk :: ThunkType -> ThunkNames
namesForThunk (ThunkType ss) =
  ThunkNames {
    thunkTypeName = "thunk_" ++ ty
  , thunkEnterName = "enter_" ++ ty
  , thunkTraceName = "trace_" ++ ty
  , thunkSuspendName = "suspend_" ++ ty
  }
  where
    ty = concatMap tycode ss

typeForSort :: Sort -> String
typeForSort (Alloc aa) = "struct alloc_header *"
typeForSort (Closure ss) = "struct closure *"
typeForSort Integer = "struct int64_value *"
typeForSort Sum = "struct sum *"
typeForSort Boolean = "struct bool_value *"
typeForSort (Pair _ _) = "struct pair *"
typeForSort Unit = "struct unit *"
typeForSort (List _) = "struct list *"

infoForSort :: EnvPtr -> Sort -> String
infoForSort envp (Alloc aa) = envp ++ "->" ++ show aa
infoForSort _ Sum = "sum_info"
infoForSort _ Boolean = "bool_value_info"
infoForSort _ Integer = "int64_value_info"
infoForSort _ (Pair _ _) = "pair_info"
infoForSort _ Unit = "unit_info"
infoForSort _ (Closure ss) = "closure_info"
infoForSort _ (List _) = "list_info"

asSort :: Sort -> String -> String
asSort (Alloc _) x = asAlloc x
asSort Integer x = "AS_INT64(" ++ x ++ ")"
asSort (Closure ss) x = "AS_CLOSURE(" ++ x ++ ")"
asSort Sum x = "AS_SUM(" ++ x ++ ")"
asSort Boolean x = "AS_BOOL(" ++ x ++ ")"
asSort (Pair _ _) x = "AS_PAIR(" ++ x ++ ")"
asSort Unit x = "AS_UNIT(" ++ x ++ ")"
asSort (List _s) x = "AS_LIST(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0..]

emitThunkDecl :: ThunkType -> [String]
emitThunkDecl t =
  emitThunkType t ++
  emitThunkEnter t ++
  emitThunkTrace t ++
  emitThunkSuspend t

emitThunkType :: ThunkType -> [String]
emitThunkType (ThunkType ss) =
  ["struct " ++ thunkTypeName ns ++ " {"
  ,"    struct thunk header;"
  ,"    struct closure *closure;"] ++
  mapWithIndex mkField ss ++
  ["};"]
  where
    ns = namesForThunk (ThunkType ss)
    mkField i s = "    " ++ emitFieldDecl (FieldName s ("arg" ++ show i)) ++ ";"

emitThunkTrace :: ThunkType -> [String]
emitThunkTrace (ThunkType ss) =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    " ++ emitMarkGray "next->closure" (Closure ss) ++ ";"] ++
  mapWithIndex traceField ss ++
  ["}"]
  where
    ns = namesForThunk (ThunkType ss)
    traceField i s = "    " ++ emitMarkGray ("next->arg" ++ show i) s ++ ";"

emitThunkEnter :: ThunkType -> [String]
emitThunkEnter (ThunkType ss) =
  ["void " ++ thunkEnterName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    void (*code)(" ++ paramList ++ ") = (void (*)(" ++ paramList ++ "))next->closure->code;"
  ,"    code(" ++ argList ++ ");"
  ,"}"]
  where
    ns = namesForThunk (ThunkType ss)
    paramList = commaSep ("void *env" : mapWithIndex makeParam ss)
    makeParam i s = emitPlace (PlaceName s ("arg" ++ show i))
    argList = commaSep ("next->closure->env" : mapWithIndex makeArgument ss)
    makeArgument i _ = "next->arg" ++ show i

emitThunkSuspend :: ThunkType -> [String]
emitThunkSuspend (ThunkType ss) =
  ["void " ++ thunkSuspendName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = realloc(next_step, sizeof(struct " ++ thunkTypeName ns ++ "));"
  ,"    next->header.enter = closure->enter;"
  ,"    next->header.trace = " ++ thunkTraceName ns ++ ";"
  ,"    next->closure = closure;"] ++
  mapWithIndex assignField ss ++
  ["    next_step = (struct thunk *)next;"
  ,"}"]
  where
    ns = namesForThunk (ThunkType ss)
    paramList = commaSep ("struct closure *closure" : mapWithIndex makeParam ss)
    makeParam i s = emitPlace (PlaceName s ("arg" ++ show i))
    assignField i _ = "    next->arg" ++ show i ++ " = arg" ++ show i ++ ";"

emitClosureDecl :: H.ClosureDecl -> [String]
emitClosureDecl (H.ClosureDecl d envd params e) =
  emitEnvDecl ns envd ++
  emitEnvTrace ns envd ++
  emitEnvAlloc ns envd ++
  emitClosureCode ns params e
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
    params = if null fs then "void" else commaSep (map emitFieldDecl fs)

    assignInfo :: InfoName -> String
    assignInfo aa = "    env->" ++ infoName aa ++ " = " ++ infoName aa ++ ";"

    assignField :: FieldName -> String
    assignField (FieldName _ x) = "    env->" ++ x ++ " = " ++ x ++ ";"

-- | Emit a method to trace a closure environment.
-- (Emit type info for the environment types)
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
    traceField (FieldName s x) = "    " ++ emitMarkGray ("env->" ++ x) s ++ ";"

emitClosureCode :: ClosureNames -> [PlaceName] -> TermH -> [String]
emitClosureCode ns xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ closureEnvName ns ++ " *" ++ envPointer ++ " = " ++ envParam ++ ";"] ++
  emitClosureBody envPointer e ++
  ["}"]
  where
    paramList = commaSep (("void *"++envParam) : map emitPlace xs)
    xs' = Set.fromList (map placeName xs) `Set.union` go2 e
    envParam = go "envp" xs'
    envPointer = go "env" (Set.insert envParam xs')

    go x vs = if Set.notMember x vs then x else go ('_':x) vs

    -- Find the set of temporaries used by this function.
    go2 (LetValH p _ e') = Set.insert (placeName p) (go2 e')
    go2 (LetPrimH p _ e') = Set.insert (placeName p) (go2 e')
    go2 (LetProjectH p _ _ e') = Set.insert (placeName p) (go2 e')
    go2 (AllocClosure cs e') = foldr (Set.insert . placeName) (go2 e') (map closurePlace cs)
    go2 (HaltH _ _) = Set.empty
    go2 (OpenH _ _ _) = Set.empty
    go2 (CaseH _ _ _) = Set.empty

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
  [emitSuspend envp c ty xs]
emitClosureBody envp (CaseH x kind ks) =
  emitCase kind envp x ks

emitSuspend :: EnvPtr -> Name -> ThunkType -> [Name] -> String
emitSuspend envp cl ty xs = "    " ++ emitPrimCall envp method (cl : xs) ++ ";"
  where
    method = thunkSuspendName (namesForThunk ty)

emitCase :: CaseKind -> EnvPtr -> Name -> [(Name, ThunkType)] -> [String]
emitCase kind envp x ks =
  ["    switch (" ++ emitName envp x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch (zip3 [0..] (branchArgNames kind) ks) ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: (Int, (String, [String]), (Name, ThunkType)) -> [String]
    emitCaseBranch (i, (ctorCast, argNames), (k, t)) =
      let
        method = thunkSuspendName (namesForThunk t)
        args = emitName envp k : zipWith mkArg argNames (thunkArgSorts t)
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
emitValueAlloc envp (ConsH s x xs) =
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
emitAlloc envp (ClosureAlloc p ty d (EnvAlloc free rec)) =
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
    envAllocArgs = map (emitName envp . snd) free ++ map (const "NULL") rec

emitPatch :: ClosureNames -> PlaceName -> EnvAlloc -> [String]
emitPatch ns (PlaceName _ p) (EnvAlloc _free rec) =
  ["    " ++ env ++ "->" ++ f ++ " = " ++ x ++ ";" | (FieldName _ f, LocalName x) <- rec]
  where env = "((struct " ++ closureEnvName ns ++ " *)" ++ p ++ "->env)"

emitFieldDecl :: FieldName -> String
emitFieldDecl (FieldName s x) = typeForSort s ++ x

emitInfoDecl :: InfoName -> String
emitInfoDecl (InfoName i) = "struct type_info " ++ i

emitPlace :: PlaceName -> String
emitPlace (PlaceName s x) = typeForSort s ++ x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = x
emitName envp (EnvName x) = envp ++ "->" ++ x

-- TODO: I think 'emitMarkGray' needs the environment pointer, so it can access
-- type_info in the env.
emitMarkGray :: String -> Sort -> String
emitMarkGray x s = "mark_gray(" ++ asAlloc x ++ ", " ++ infoForSort "NULL" s ++ ")"

