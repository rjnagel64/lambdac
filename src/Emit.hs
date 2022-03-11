
module Emit (emitProgram) where

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (intercalate)

import qualified Hoist as H
import Hoist

-- TODO: Something smarter than string and list concatenation.
-- builders? text? environment?

emitProgram :: (HoistDecls, TermH) -> [String]
emitProgram (HoistDecls (ts, cs), e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap emitClosureDecl cs ++
  emitEntryPoint e

data DeclNames
  = DeclNames {
    declEnvName :: String
  , declAllocName :: String
  , declTraceName :: String
  , declCodeName :: String
  }

namesForDecl :: DeclName -> DeclNames
namesForDecl (DeclName f) =
  DeclNames {
    declEnvName = f ++ "_env"
  , declAllocName = "allocate_" ++ f ++ "_env"
  , declTraceName = "trace_" ++ f ++ "_env"
  , declCodeName = f ++ "_code"
  }

prologue :: [String]
prologue = ["#include \"rts.h\""]

emitEntryPoint :: TermH -> [String]
emitEntryPoint e =
  ["void program_entry(void) {"] ++
  emitClosureBody e ++
  ["}"]

data ThunkNames
  = ThunkNames {
    thunkTypeName :: String
  , thunkEnterName :: String
  , thunkTraceName :: String
  , thunkSuspendName :: String
  }

namesForThunk :: ThunkType -> ThunkNames
namesForThunk (ThunkType ss) =
  ThunkNames {
    thunkTypeName = "thunk_" ++ tycode
  , thunkEnterName = "enter_" ++ tycode
  , thunkTraceName = "trace_" ++ tycode
  , thunkSuspendName = "suspend_" ++ tycode
  }
  where
    -- This scheme will almost certainly break down as types get fancier.
    tycode = map code ss
    code Closure = 'C'
    code Value = 'V'
    code Alloc = 'A'

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
  map mkField ss' ++
  ["};"]
  where
    ns = namesForThunk (ThunkType ss)
    ss' = zip [0..] ss :: [(Int, Sort)]
    mkField (i, s) = "    " ++ emitFieldDecl (FieldName s ("arg" ++ show i)) ++ ";"

emitThunkTrace :: ThunkType -> [String]
emitThunkTrace (ThunkType ss) =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    mark_gray(" ++ asSort Alloc "next->closure" ++ ");"] ++
  map traceField ss' ++
  ["}"]
  where
    ns = namesForThunk (ThunkType ss)
    ss' = zip [0..] ss :: [(Int, Sort)]
    traceField (i, _s) = "    mark_gray(" ++ asSort Alloc ("next->arg" ++ show i) ++ ");"

emitThunkEnter :: ThunkType -> [String]
emitThunkEnter (ThunkType ss) =
  ["void " ++ thunkEnterName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    void (*code)(" ++ paramList ++ ") = (void (*)(" ++ paramList ++ "))next->closure->code;"
  ,"    code(" ++ argList ++ ");"
  ,"}"]
  where
    ns = namesForThunk (ThunkType ss)
    ss' = zip [0..] ss :: [(Int, Sort)]
    paramList = intercalate ", " ("void *env" : map makeParam ss')
    makeParam (i, s) = emitPlace (PlaceName s ("arg" ++ show i))
    argList = intercalate ", " ("next->closure->env" : map makeArgument ss')
    makeArgument (i, _) = "next->arg" ++ show i

emitThunkSuspend :: ThunkType -> [String]
emitThunkSuspend (ThunkType ss) =
  ["void " ++ thunkSuspendName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = realloc(next_step, sizeof(struct " ++ thunkTypeName ns ++ "));"
  ,"    next->header.enter = " ++ thunkEnterName ns ++ ";"
  ,"    next->header.trace = " ++ thunkTraceName ns ++ ";"
  ,"    next->closure = closure;"] ++
  map assignField ss' ++
  ["    next_step = (struct thunk *)next;"
  ,"}"]
  where
    ns = namesForThunk (ThunkType ss)
    ss' = zip [0..] ss :: [(Int, Sort)]
    paramList = intercalate ", " ("struct closure *closure" : map makeParam ss')
    makeParam (i, s) = emitPlace (PlaceName s ("arg" ++ show i))
    assignField (i, _) = "    next->arg" ++ show i ++ " = arg" ++ show i ++ ";"

emitClosureDecl :: H.ClosureDecl -> [String]
emitClosureDecl (H.ClosureDecl d envd params e) =
  emitEnvDecl ns envd ++
  emitEnvAlloc ns envd ++
  emitEnvTrace ns envd ++
  emitClosureCode ns params e
  where ns = namesForDecl d

emitEnvDecl :: DeclNames -> EnvDecl -> [String]
emitEnvDecl ns (EnvDecl fs) =
  ["struct " ++ declEnvName ns ++ " {"] ++
  map mkField fs ++
  ["};"]
  where
    mkField f = "    " ++ emitFieldDecl f ++ ";"

emitEnvAlloc :: DeclNames -> EnvDecl -> [String]
emitEnvAlloc ns (EnvDecl []) =
  ["struct " ++ declEnvName ns ++ " *" ++ declAllocName ns ++ "(void) {"
  ,"    return NULL;"
  ,"}"]
emitEnvAlloc ns (EnvDecl fs) =
  -- TODO: What if there is a parameter named 'env'?
  ["struct " ++ declEnvName ns ++ " *" ++ declAllocName ns ++ "(" ++ params ++ ") {"] ++
  ["    struct " ++ declEnvName ns ++ " *env = malloc(sizeof(struct " ++ declEnvName ns ++ "));"] ++
  map assignField fs ++
  ["    return env;"
  ,"}"]
  where
    params = intercalate ", " (map emitFieldDecl fs)

    assignField :: FieldName -> String
    assignField (FieldName _ x) = "    env->" ++ x ++ " = " ++ x ++ ";"

-- | Emit a method to trace a closure environment.
-- We do not need to worry about shadowing the name 'env' here because 'envp'
-- and 'env' are the only local variables in this function.
emitEnvTrace :: DeclNames -> EnvDecl -> [String]
emitEnvTrace ns (EnvDecl fs) =
  ["void " ++ declTraceName ns ++ "(void *envp) {"
  ,"    struct " ++ declEnvName ns ++ " *env = envp;"] ++
  map traceField fs ++
  ["}"]
  where
    traceField :: FieldName -> String
    traceField (FieldName _ x) = "    mark_gray(" ++ asSort Alloc ("env->" ++ x) ++ ");"

-- TODO: What if 'env' is the name that gets shadowed? (I.e., the function
-- parameter is named 'env')
-- Find the set of names used by this closure, and rename 'env' and 'envp'
-- until they are not in that set. (Actually, if I use a generic function
-- pointer in the generic closure value, I can have `struct $(declEnvName ns)
-- *env` directly, instead of needing `env` and `envp`.)
emitClosureCode :: DeclNames -> [PlaceName] -> TermH -> [String]
emitClosureCode ns [] e =
  ["void " ++ declCodeName ns ++ "(void *envp) {"
  ,"    struct " ++ declEnvName ns ++ " *env = envp;"] ++
  emitClosureBody e ++
  ["}"]
emitClosureCode ns xs e =
  ["void " ++ declCodeName ns ++ "(void *envp, " ++ emitParameterList xs ++ ") {"
  ,"    struct " ++ declEnvName ns ++ " *env = envp;"] ++
  emitClosureBody e ++
  ["}"]

emitParameterList :: [PlaceName] -> String
emitParameterList ps = intercalate ", " (map emitPlace ps)

emitClosureBody :: TermH -> [String]
emitClosureBody (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValueAlloc v ++ ";"] ++
  emitClosureBody e
emitClosureBody (LetFstH x y e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) ("project_fst(" ++ emitName y ++ ")") ++ ";"] ++
  emitClosureBody e
emitClosureBody (LetSndH x y e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) ("project_snd(" ++ emitName y ++ ")") ++ ";"] ++
  emitClosureBody e
emitClosureBody (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp p ++ ";"] ++
  emitClosureBody e
emitClosureBody (AllocClosure cs e) =
  emitAllocGroup cs ++
  emitClosureBody e
emitClosureBody (HaltH x) =
  ["    halt_with(" ++ asSort Alloc (emitName x) ++ ");"]
emitClosureBody (OpenH c xs) =
  [emitSuspend c xs]
emitClosureBody (CaseH x (k1, t) (k2, s)) =
  emitCase x [(k1, t), (k2, s)]

emitSuspend :: Name -> [(Name, Sort)] -> String
emitSuspend cl xs = "    " ++ method ++ "(" ++ intercalate ", " args ++ ");"
  where
    method = thunkSuspendName (namesForThunk (ThunkType (map snd xs)))
    args = emitName cl : map (emitName . fst) xs

emitCase :: Name -> [(Name, ThunkType)] -> [String]
emitCase x ks =
  ["    switch (" ++ emitName x ++ "->words[0]) {"] ++
  concatMap emitCaseBranch (zip [0..] ks) ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: (Int, (Name, ThunkType)) -> [String]
    emitCaseBranch (i, (k, t)) = case t of 
      ThunkType [] ->
        let method = thunkSuspendName (namesForThunk t) in
        let args = [emitName k] in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ intercalate ", " args ++ ");"
        ,"        break;"]
      ThunkType [s] -> 
        let method = thunkSuspendName (namesForThunk t) in
        let args = [emitName k, asSort s (emitName x ++ "->words[1]")] in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ intercalate ", " args ++ ");"
        ,"        break;"]
      ThunkType _ -> error "multi-argument case branches not yet supported."

emitValueAlloc :: ValueH -> String
emitValueAlloc (IntH i) = "allocate_int32(" ++ show i ++ ")"
emitValueAlloc (BoolH True) = "allocate_true()"
emitValueAlloc (BoolH False) = "allocate_false()"
emitValueAlloc NilH = "allocate_nil()"
emitValueAlloc (PairH y z) = "allocate_pair(" ++ emitName y ++ ", " ++ emitName z ++ ")"
emitValueAlloc (InlH y) = "allocate_inl(" ++ emitName y ++ ")"
emitValueAlloc (InrH y) = "allocate_inr(" ++ emitName y ++ ")"

emitPrimOp :: PrimOp -> String
emitPrimOp (PrimAddInt32 x y) = "prim_addint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimSubInt32 x y) = "prim_subint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimMulInt32 x y) = "prim_mulint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimEqInt32 x y) = "prim_eqint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimNeInt32 x y) = "prim_neint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimLtInt32 x y) = "prim_ltint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimLeInt32 x y) = "prim_leint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimGtInt32 x y) = "prim_gtint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimGeInt32 x y) = "prim_geint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"

asSort :: Sort -> String -> String
asSort Alloc x = "AS_ALLOC(" ++ x ++ ")"
asSort Value x = "AS_VALUE(" ++ x ++ ")"
asSort Closure x = "AS_CLOSURE(" ++ x ++ ")"

emitAllocGroup :: [ClosureAlloc] -> [String]
emitAllocGroup closures =
  map (\ (ClosureAlloc p d env) -> emitAlloc bindGroup p d env) closures ++
  concatMap (\ (ClosureAlloc p d env) -> emitPatch (namesForDecl d) bindGroup p env) closures
  where
    bindGroup = Set.fromList $ [d | ClosureAlloc _ (DeclName d) _ <- closures]

-- Names in bindGroup -> NULL
emitAlloc :: Set String -> PlaceName -> DeclName -> EnvAlloc -> String
emitAlloc bindGroup p d (EnvAlloc xs) =
  "    " ++ emitPlace p ++ " = " ++ "allocate_closure" ++ "(" ++ intercalate ", " args ++ ");"
  where
    ns = namesForDecl d
    args = [envArg, traceArg, "(void (*)(void))" ++ codeArg]
    -- Allocate closure environment here, with NULL for cyclic captures.
    envArg = declAllocName ns ++ "(" ++ intercalate ", " (map (allocArg . snd) xs) ++ ")"
    allocArg (LocalName x) = if Set.member x bindGroup then "NULL" else x
    allocArg (EnvName x) = "env->" ++ x -- TODO: What if environment has different name?
    codeArg = declCodeName ns
    traceArg = declTraceName ns

emitPatch :: DeclNames -> Set String -> PlaceName -> EnvAlloc -> [String]
emitPatch ns bindGroup (PlaceName _ p) (EnvAlloc xs) =
  ["    " ++ env ++ "->" ++ f ++ " = " ++ x ++ ";" | (FieldName _ f, LocalName x) <- xs, Set.member x bindGroup]
  where env = "((struct " ++ declEnvName ns ++ " *)" ++ p ++ "->env)"

emitFieldDecl :: FieldName -> String
emitFieldDecl (FieldName Closure c) = "struct closure *" ++ c
emitFieldDecl (FieldName Value x) = "struct value *" ++ x
emitFieldDecl (FieldName Alloc a) = "struct alloc_header *" ++ a

emitPlace :: PlaceName -> String
emitPlace (PlaceName Closure k) = "struct closure *" ++ k
emitPlace (PlaceName Value x) = "struct value *" ++ x
emitPlace (PlaceName Alloc a) = "struct alloc_header *" ++ a

-- TODO: Parametrize this by what the name of the environment pointer is.
-- There may be situations where 'env' or 'envp' is the name of a parameter.
emitName :: Name -> String
emitName (LocalName x) = x
emitName (EnvName x) = "env->" ++ x

