
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

emitProgram :: (Set ThunkType, Set ProductType, [ClosureDecl], TermH) -> [String]
emitProgram (ts, ps, cs, e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap emitProductDecl ps ++
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

-- This scheme will almost certainly break down as types get fancier.
tycode :: Sort -> String
tycode Closure = "C"
tycode Value = "V"
tycode Alloc = "A"
tycode Sum = "S"
tycode (Product ss) = 'P' : show (length ss) ++ concatMap tycode ss

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
  ,"    next->header.enter = closure->enter;"
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

emitProductDecl :: ProductType -> [String]
emitProductDecl (ProductType ss) =
  ["struct product *allocate_" ++ ty ++ "(" ++ intercalate ", " args ++ ") {"
  ,"    struct product *v = malloc(sizeof(struct product) + " ++ numFields ++ " * sizeof(uintptr_t));"
  ,"    v->header.type = ALLOC_PROD;"
  ,"    v->num_fields = " ++ numFields ++ ";"] ++
  map assignField iss ++
  ["    cons_new_alloc(AS_ALLOC(v));"
  ,"    return v;"
  ,"}"]
  where
    numFields = show (length ss)
    ty = tycode (Product ss)
    iss = zip [0..] ss :: [(Int, Sort)]
    args = if null ss then ["void"] else map emitPlace [PlaceName s ("arg" ++ show i) | (i, s) <- iss]
    assignField (i, s) = "    v->words[" ++ show i ++ "] = (uintptr_t)arg" ++ show i ++ ";"

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
    paramList = intercalate ", " (("void *"++envParam) : map emitPlace xs)
    xs' = Set.fromList (map placeName xs) `Set.union` go2 e
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
    go2 (CaseH _ _) = Set.empty

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
emitClosureBody envp (CaseH x ks) =
  emitCase envp x ks

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
emitValueAlloc _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc _ (BoolH True) = "allocate_true()"
emitValueAlloc _ (BoolH False) = "allocate_false()"
emitValueAlloc envp (ProdH xs) =
  "allocate_" ++ ty ++ "(" ++ intercalate ", " args ++ ")"
  where
    ty = tycode (Product (map snd xs))
    args = map (emitName envp . fst) xs
emitValueAlloc envp (InlH y) = "allocate_inl(" ++ asSort Alloc (emitName envp y) ++ ")"
emitValueAlloc envp (InrH y) = "allocate_inr(" ++ asSort Alloc (emitName envp y) ++ ")"

emitPrimOp :: String -> PrimOp -> String
emitPrimOp envp (PrimAddInt64 x y) = emitPrimCall envp "prim_addint64" [x, y]
emitPrimOp envp (PrimSubInt64 x y) = emitPrimCall envp "prim_subint64" [x, y]
emitPrimOp envp (PrimMulInt64 x y) = emitPrimCall envp "prim_mulint64" [x, y]
emitPrimOp envp (PrimEqInt64 x y) = emitPrimCall envp "prim_eqint64" [x, y]
emitPrimOp envp (PrimNeInt64 x y) = emitPrimCall envp "prim_neint64" [x, y]
emitPrimOp envp (PrimLtInt64 x y) = emitPrimCall envp "prim_ltint64" [x, y]
emitPrimOp envp (PrimLeInt64 x y) = emitPrimCall envp "prim_leint64" [x, y]
emitPrimOp envp (PrimGtInt64 x y) = emitPrimCall envp "prim_gtint64" [x, y]
emitPrimOp envp (PrimGeInt64 x y) = emitPrimCall envp "prim_geint64" [x, y]

emitPrimCall :: String -> String -> [Name] -> String
emitPrimCall envp f xs = f ++ "(" ++ intercalate ", " (map (emitName envp) xs) ++ ")"

asSort :: Sort -> String -> String
asSort Alloc x = "AS_ALLOC(" ++ x ++ ")"
asSort Value x = "AS_CONST(" ++ x ++ ")"
asSort Closure x = "AS_CLOSURE(" ++ x ++ ")"
asSort Sum x = "AS_SUM(" ++ x ++ ")"
asSort (Product ss) x = "AS_PRODUCT(" ++ x ++ ")"

-- TODO: Generalize emitAllocGroup and merge it with emitValueAlloc, to support
-- allocating mutually-recursive values, of which closures are merely one
-- example. (Eventually, I believe this will let me generalize 'let fun' to
-- 'let rec x1 = e1; ...'.)
-- (I probably need to restrict this to having an outermost ctor, so that there
-- are fields to update. 'let x = x + 1; in x' doesn't make much sense, and
-- can't really be implemented.)
emitAllocGroup :: String -> [ClosureAlloc] -> [String]
emitAllocGroup envp closures =
  map (emitAlloc envp) closures ++
  concatMap (\ (ClosureAlloc p _ty d env) -> emitPatch (namesForDecl d) p env) closures

emitAlloc :: String -> ClosureAlloc -> String
emitAlloc envp (ClosureAlloc p ty d (EnvAlloc free rec)) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ intercalate ", " args ++ ");"
  where
    ns = namesForDecl d
    args = [envArg, traceArg, codeArg, enterArg]
    envArg = declAllocName ns ++ "(" ++ intercalate ", " envAllocArgs ++ ")"
    traceArg = declTraceName ns
    codeArg = "(void (*)(void))" ++ declCodeName ns
    enterArg = thunkEnterName (namesForThunk ty)

    -- Recursive/cyclic environment references are initialized to NULL, and
    -- then patched once all the closures have been allocated.
    envAllocArgs = map (emitName envp . snd) free ++ map (const "NULL") rec

emitPatch :: DeclNames -> PlaceName -> EnvAlloc -> [String]
emitPatch ns (PlaceName _ p) (EnvAlloc _free rec) =
  ["    " ++ env ++ "->" ++ f ++ " = " ++ x ++ ";" | (FieldName _ f, LocalName x) <- rec]
  where env = "((struct " ++ declEnvName ns ++ " *)" ++ p ++ "->env)"

emitFieldDecl :: FieldName -> String
emitFieldDecl (FieldName Closure c) = "struct closure *" ++ c
emitFieldDecl (FieldName Value x) = "struct constant *" ++ x
emitFieldDecl (FieldName Alloc a) = "struct alloc_header *" ++ a
emitFieldDecl (FieldName Sum x) = "struct sum *" ++ x
emitFieldDecl (FieldName (Product ss) x) = "struct product *" ++ x

emitPlace :: PlaceName -> String
emitPlace (PlaceName Closure k) = "struct closure *" ++ k
emitPlace (PlaceName Value x) = "struct constant *" ++ x
emitPlace (PlaceName Alloc a) = "struct alloc_header *" ++ a
emitPlace (PlaceName Sum x) = "struct sum *" ++ x
emitPlace (PlaceName (Product ss) x) = "struct product *" ++ x

emitName :: String -> Name -> String
emitName _ (LocalName x) = x
emitName envp (EnvName x) = envp ++ "->" ++ x

