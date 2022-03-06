
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
  ,"    trace_closure(next->closure);"] ++
  map traceField ss' ++
  ["}"]
  where
    ns = namesForThunk (ThunkType ss)
    ss' = zip [0..] ss :: [(Int, Sort)]
    traceField (i, s) = "    trace_" ++ show s ++ "(next->arg" ++ show i ++ ");"

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
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
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
    traceField (FieldName Closure c) = "    trace_closure(env->" ++ c ++ ");"
    traceField (FieldName Value x) = "    trace_value(env->" ++ x ++ ");"
    traceField (FieldName Alloc a) = "    trace_alloc(env->" ++ a ++ ");"

-- TODO: What if 'env' is the name that gets shadowed? (I.e., the function
-- parameter is named 'env')
-- Find the set of names used by this closure, and rename 'env' and 'envp'
-- until they are not in that set. (Actually, if I use a generic function
-- pointer in the generic closure value, I can have `struct $(declEnvName ns)
-- *env` directly, instead of needing `env` and `envp`.)
emitClosureCode :: DeclNames -> [PlaceName] -> TermH -> [String]
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
  ["    " ++ emitPlace x ++ " = AS_VALUE(project_fst(" ++ emitName y ++ "));"] ++
  emitClosureBody e
emitClosureBody (LetSndH x y e) =
  ["    " ++ emitPlace x ++ " = AS_VALUE(project_snd(" ++ emitName y ++ "));"] ++
  emitClosureBody e
emitClosureBody (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp p ++ ";"] ++
  emitClosureBody e
emitClosureBody (AllocClosure cs e) =
  emitAllocGroup cs ++
  emitClosureBody e
emitClosureBody (HaltH x) =
  ["    halt_with(" ++ asAlloc (emitName x) ++ ");"]
emitClosureBody (JumpH k x) =
  [emitSuspend "suspend_jump" [emitName k, asAlloc (emitName x)]]
emitClosureBody (CallH f x k) =
  [emitSuspend "suspend_call" [emitName f, asAlloc (emitName x), emitName k]]
emitClosureBody (CaseH x k1 k2) =
  emitCase x [k1, k2]

-- TODO: I would prefer to take a list of names here, but I sometimes need to
-- call 'asAlloc' for stupid reasons.
-- TODO: The thunk type is determined by the closure type of the first argument.
--
-- emitSuspend :: (Name, ClosureType) -> [Name] -> String
emitSuspend :: String -> [String] -> String
emitSuspend suspend args = "    " ++ suspend ++ "(" ++ intercalate ", " args ++ ");"

emitCase :: Name -> [Name] -> [String]
emitCase x ks =
  ["    switch (" ++ emitName x ++ "->words[0]) {"] ++
  concatMap emitCaseBranch (zip [0..] ks) ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: (Int, Name) -> [String]
    emitCaseBranch (i, k) =
      ["    case " ++ show i ++ ":"
      -- TODO: Use the correct thunk suspension method here. (the closure type
      -- of k determines what suspension to use.)
      -- (Use type info (x :: A + B) in order to cast the words[1] to the
      -- correct sort (A if 0, B if 1), as well.)
      ,"    " ++ emitSuspend "suspend_jump" [emitName k, asAlloc (emitName x ++ "->words[1]")]
      ,"        break;"]

emitValueAlloc :: ValueH -> String
emitValueAlloc (IntH i) = "allocate_int32(" ++ show i ++ ")"
emitValueAlloc NilH = "allocate_nil()"
emitValueAlloc (PairH y z) = "allocate_pair(" ++ emitName y ++ ", " ++ emitName z ++ ")"
emitValueAlloc (InlH y) = "allocate_inl(" ++ emitName y ++ ")"
emitValueAlloc (InrH y) = "allocate_inr(" ++ emitName y ++ ")"

emitPrimOp :: PrimOp -> String
emitPrimOp (PrimAddInt32 x y) = "prim_addint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimSubInt32 x y) = "prim_subint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimMulInt32 x y) = "prim_mulint32(" ++ emitName x ++ ", " ++ emitName y ++ ")"
emitPrimOp (PrimIsZero32 x) = "prim_iszero32(" ++ emitName x ++ ")"

-- | Cast a value to an arbitrary allocation.
-- Ultimately, I expect not to need this, because arbitrary allocations are the
-- representation of polymorphic values, and the typechecker will rule out
-- cases like 'expected a, got int' and 'expected int, got a'.
-- The other factor obviating the need for this function is that smarter
-- calling conventions will use more precise types, rather than always
-- accepting `struct alloc_header *`.
asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"

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

