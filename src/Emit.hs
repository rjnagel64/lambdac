
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

emitProgram :: (Set ThunkType, [ClosureDecl], TermH) -> [String]
emitProgram (ts, cs, e) =
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
    code Sum = 'S'

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

emitClosureCode :: DeclNames -> [PlaceName] -> TermH -> [String]
emitClosureCode ns xs e =
  ["void " ++ declCodeName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ declEnvName ns ++ " *" ++ envPointer ++ " = " ++ envParam ++ ";"] ++
  emitClosureBody envPointer e ++
  ["}"]
  where
    paramList = if null xs then "void *envp" else "void *envp, " ++ emitParameterList xs
    xs' = Set.fromList (map placeName (xs)) `Set.union` go2 e
    envParam = go "envp" xs'
    envPointer = go "env" (Set.insert envParam xs')

    go x vs = if Set.notMember x vs then x else go ('_':x) vs

    -- Find the set of temporaries used by this function.
    go2 (LetValH p _ e') = Set.insert (placeName p) (go2 e')
    go2 (LetPrimH p _ e') = Set.insert (placeName p) (go2 e')
    go2 (LetFstH p _ e') = Set.insert (placeName p) (go2 e')
    go2 (LetSndH p _ e') = Set.insert (placeName p) (go2 e')
    go2 (AllocClosure cs e') = foldr (Set.insert . placeName) (go2 e') (map closurePlace cs)
    go2 (HaltH _) = Set.empty
    go2 (OpenH _ _) = Set.empty
    go2 (CaseH _ _ _) = Set.empty

emitParameterList :: [PlaceName] -> String
emitParameterList ps = intercalate ", " (map emitPlace ps)

emitClosureBody :: String -> TermH -> [String]
emitClosureBody envp (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValueAlloc envp v ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (LetFstH x y e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) ("project_fst(" ++ emitName envp y ++ ")") ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (LetSndH x y e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) ("project_snd(" ++ emitName envp y ++ ")") ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp envp p ++ ";"] ++
  emitClosureBody envp e
emitClosureBody envp (AllocClosure cs e) =
  emitAllocGroup envp cs ++
  emitClosureBody envp e
emitClosureBody envp (HaltH x) =
  ["    halt_with(" ++ asSort Alloc (emitName envp x) ++ ");"]
emitClosureBody envp (OpenH c xs) =
  [emitSuspend envp c xs]
emitClosureBody envp (CaseH x (k1, t) (k2, s)) =
  emitCase envp x [(k1, t), (k2, s)]

emitSuspend :: String -> Name -> [(Name, Sort)] -> String
emitSuspend envp cl xs = "    " ++ method ++ "(" ++ intercalate ", " args ++ ");"
  where
    method = thunkSuspendName (namesForThunk (ThunkType (map snd xs)))
    args = emitName envp cl : map (emitName envp . fst) xs

emitCase :: String -> Name -> [(Name, ThunkType)] -> [String]
emitCase envp x ks =
  ["    switch (" ++ emitName envp x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch (zip [0..] ks) ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: (Int, (Name, ThunkType)) -> [String]
    emitCaseBranch (i, (k, t)) =
      let
        method = thunkSuspendName (namesForThunk t)
        mkArg :: (Int, Sort) -> String
        mkArg (j, s) = asSort s (emitName envp x ++ "->words[" ++ show j ++ "]")
        args = emitName envp k : map mkArg (zip [0..] (thunkArgSorts t))
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ intercalate ", " args ++ ");"
        ,"        break;"]

emitValueAlloc :: String -> ValueH -> String
emitValueAlloc _ (IntH i) = "allocate_int32(" ++ show i ++ ")"
emitValueAlloc _ (BoolH True) = "allocate_true()"
emitValueAlloc _ (BoolH False) = "allocate_false()"
emitValueAlloc _ NilH = "allocate_nil()"
emitValueAlloc envp (PairH y z) = "allocate_pair(" ++ asSort Alloc (emitName envp y) ++ ", " ++ asSort Alloc (emitName envp z) ++ ")"
emitValueAlloc envp (InlH y) = "allocate_inl(" ++ asSort Alloc (emitName envp y) ++ ")"
emitValueAlloc envp (InrH y) = "allocate_inr(" ++ asSort Alloc (emitName envp y) ++ ")"

emitPrimOp :: String -> PrimOp -> String
emitPrimOp envp (PrimAddInt32 x y) = emitPrimCall envp "prim_addint32" [x, y]
emitPrimOp envp (PrimSubInt32 x y) = emitPrimCall envp "prim_subint32" [x, y]
emitPrimOp envp (PrimMulInt32 x y) = emitPrimCall envp "prim_mulint32" [x, y]
emitPrimOp envp (PrimEqInt32 x y) = emitPrimCall envp "prim_eqint32" [x, y]
emitPrimOp envp (PrimNeInt32 x y) = emitPrimCall envp "prim_neint32" [x, y]
emitPrimOp envp (PrimLtInt32 x y) = emitPrimCall envp "prim_ltint32" [x, y]
emitPrimOp envp (PrimLeInt32 x y) = emitPrimCall envp "prim_leint32" [x, y]
emitPrimOp envp (PrimGtInt32 x y) = emitPrimCall envp "prim_gtint32" [x, y]
emitPrimOp envp (PrimGeInt32 x y) = emitPrimCall envp "prim_geint32" [x, y]

emitPrimCall :: String -> String -> [Name] -> String
emitPrimCall envp f xs = f ++ "(" ++ intercalate ", " (map (emitName envp) xs) ++ ")"

asSort :: Sort -> String -> String
asSort Alloc x = "AS_ALLOC(" ++ x ++ ")"
asSort Value x = "AS_VALUE(" ++ x ++ ")"
asSort Closure x = "AS_CLOSURE(" ++ x ++ ")"
asSort Sum x = "AS_SUM(" ++ x ++ ")"

emitAllocGroup :: String -> [ClosureAlloc] -> [String]
emitAllocGroup envp closures =
  map (\ (ClosureAlloc p d env) -> emitAlloc envp bindGroup p d env) closures ++
  concatMap (\ (ClosureAlloc p d env) -> emitPatch (namesForDecl d) bindGroup p env) closures
  where
    bindGroup = Set.fromList $ [d | ClosureAlloc _ (DeclName d) _ <- closures]

-- Names in bindGroup -> NULL
emitAlloc :: String -> Set String -> PlaceName -> DeclName -> EnvAlloc -> String
emitAlloc envp bindGroup p d (EnvAlloc xs) =
  "    " ++ emitPlace p ++ " = " ++ "allocate_closure" ++ "(" ++ intercalate ", " args ++ ");"
  where
    ns = namesForDecl d
    args = [envArg, traceArg, codeArg]
    -- Allocate closure environment here, with NULL for cyclic captures.
    envArg = declAllocName ns ++ "(" ++ intercalate ", " (map (allocArg . snd) xs) ++ ")"
    traceArg = declTraceName ns
    codeArg = "(void (*)(void))" ++ declCodeName ns

    allocArg (LocalName x) | Set.member x bindGroup = "NULL"
    allocArg x = emitName envp x

emitPatch :: DeclNames -> Set String -> PlaceName -> EnvAlloc -> [String]
emitPatch ns bindGroup (PlaceName _ p) (EnvAlloc xs) =
  ["    " ++ env ++ "->" ++ f ++ " = " ++ x ++ ";" | (FieldName _ f, LocalName x) <- xs, Set.member x bindGroup]
  where env = "((struct " ++ declEnvName ns ++ " *)" ++ p ++ "->env)"

emitFieldDecl :: FieldName -> String
emitFieldDecl (FieldName Closure c) = "struct closure *" ++ c
emitFieldDecl (FieldName Value x) = "struct value *" ++ x
emitFieldDecl (FieldName Alloc a) = "struct alloc_header *" ++ a
emitFieldDecl (FieldName Sum x) = "struct sum *" ++ x

emitPlace :: PlaceName -> String
emitPlace (PlaceName Closure k) = "struct closure *" ++ k
emitPlace (PlaceName Value x) = "struct value *" ++ x
emitPlace (PlaceName Alloc a) = "struct alloc_header *" ++ a
emitPlace (PlaceName Sum x) = "struct sum *" ++ x

emitName :: String -> Name -> String
emitName _ (LocalName x) = x
emitName envp (EnvName x) = envp ++ "->" ++ x

