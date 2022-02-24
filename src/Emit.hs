
module Emit (emitProgram) where

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (intercalate)

import qualified Hoist as H
import Hoist

emitProgram :: ([H.TopDecl], TermH) -> [String]
emitProgram (ds, e) = prologue ++ concatMap emitTopDecl ds ++ emitEntryPoint e

data DeclNames
  = DeclNames {
    declEnvName :: String
  , declAllocName :: String
  , declCodeName :: String
  , declTraceName :: String
  }

namesForDecl :: DeclName -> DeclNames
namesForDecl (DeclName f) =
  DeclNames {
    declEnvName = f ++ "_env"
  , declAllocName = "allocate_" ++ f ++ "_env"
  , declCodeName = f ++ "_code"
  , declTraceName = "trace_" ++ f ++ "_env"
  }

prologue :: [String]
prologue = ["#include \"rts.h\""]

emitEntryPoint :: TermH -> [String]
emitEntryPoint e =
  ["void program_entry(void) {"] ++
  emitClosureBody e ++
  ["}"]

emitTopDecl :: TopDecl -> [String]
emitTopDecl (TopFun fs) = concatMap emitFunDecl fs
emitTopDecl (TopCont ks) = concatMap emitContDecl ks

-- TODO: Bind groups have to be emitted all at once so that proper ordering can
-- be achieved. (Or not? All recursive occurrences happen through closure
-- fields.)
emitFunDecl :: H.FunDecl -> [String]
emitFunDecl (H.FunDecl d envd x k e) =
  emitEnvDecl ns envd ++ emitEnvAlloc ns envd ++ emitEnvTrace ns envd ++ emitFunCode ns x k e
  where ns = namesForDecl d

emitContDecl :: H.ContDecl -> [String]
emitContDecl (H.ContDecl d envd x e) =
  emitEnvDecl ns envd ++ emitEnvAlloc ns envd ++ emitEnvTrace ns envd ++ emitContCode ns x e
  where ns = namesForDecl d

emitEnvDecl :: DeclNames -> EnvDecl -> [String]
emitEnvDecl ns (EnvDecl fs) =
  ["struct " ++ declEnvName ns ++ " {"] ++
  map mkField fs ++
  ["};"]
  where
    mkField (FieldName Fun f) = "    struct fun *" ++ f ++ ";";
    mkField (FieldName Cont k) = "    struct cont *" ++ k ++ ";";
    mkField (FieldName Value x) = "    struct value *" ++ x ++ ";"

-- TODO: Remember to include allocation header
emitEnvAlloc :: DeclNames -> EnvDecl -> [String]
emitEnvAlloc ns (EnvDecl []) =
  ["struct " ++ declEnvName ns ++ " *" ++ declAllocName ns ++ "(void) {"
  ,"    return NULL;"
  ,"}"]
emitEnvAlloc ns (EnvDecl fs) =
  ["struct " ++ declEnvName ns ++ " *" ++ declAllocName ns ++ "(" ++ params ++ ") {"] ++
  ["    struct " ++ declEnvName ns ++ " *env = malloc(sizeof(struct " ++ declEnvName ns ++ "));"] ++
  map assignField fs ++
  ["    return env;"
  ,"}"]
  where
    params = intercalate ", " (map mkParam fs)

    mkParam (FieldName Fun f) = "struct fun *" ++ f
    mkParam (FieldName Cont f) = "struct cont *" ++ f
    mkParam (FieldName Value f) = "struct value *" ++ f

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
    traceField (FieldName Fun f) = "    trace_fun(env->" ++ f ++ ");"
    traceField (FieldName Cont k) = "    trace_cont(env->" ++ k ++ ");"
    traceField (FieldName Value x) = "    trace_value(env->" ++ x ++ ");"

-- TODO: What if 'env' is the name that gets shadowed? (I.e., the function
-- parameter is named 'env')
emitFunCode :: DeclNames -> PlaceName -> PlaceName -> TermH -> [String]
emitFunCode ns x k e =
  ["void " ++ declCodeName ns ++ "(void *envp, " ++ emitPlace x ++ ", " ++ emitPlace k ++ ") {"
  ,"    struct " ++ declEnvName ns ++ " *env = envp;"] ++
  -- TODO: Allocate locals.
  emitClosureBody e ++
  ["}"]

emitContCode :: DeclNames -> PlaceName -> TermH -> [String]
emitContCode ns x e =
  ["void " ++ declCodeName ns ++ "(void *envp, " ++ emitPlace x ++ ") {"
  ,"    struct " ++ declEnvName ns ++ " *env = envp;"] ++
  -- TODO: Allocate locals.
  emitClosureBody e ++
  ["}"]

emitClosureBody :: TermH -> [String]
emitClosureBody (LetValH x (IntH i) e) =
  ["    " ++ emitPlace x ++ " = allocate_int32(" ++ show i ++ ");"] ++
  emitClosureBody e
emitClosureBody (LetValH x NilH e) =
  ["    " ++ emitPlace x ++ " = allocate_nil();"] ++
  emitClosureBody e
emitClosureBody (LetValH x (PairH y z) e) =
  ["    " ++ emitPlace x ++ " = allocate_pair(" ++ emitName y ++ ", " ++ emitName z ++ ");"] ++
  emitClosureBody e
emitClosureBody (LetValH x (InlH y) e) =
  ["    " ++ emitPlace x ++ " = allocate_inl(" ++ emitName y ++ ");"] ++
  emitClosureBody e
emitClosureBody (LetValH x (InrH y) e) =
  ["    " ++ emitPlace x ++ " = allocate_inr(" ++ emitName y ++ ");"] ++
  emitClosureBody e
emitClosureBody (LetFstH x y e) =
  ["    " ++ emitPlace x ++ " = project_fst(" ++ emitName y ++ ");"] ++
  emitClosureBody e
emitClosureBody (LetSndH x y e) =
  ["    " ++ emitPlace x ++ " = project_snd(" ++ emitName y ++ ");"] ++
  emitClosureBody e
emitClosureBody (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp p ++ ";"] ++
  emitClosureBody e
emitClosureBody (AllocFun fs e) = emitFunAlloc fs ++ emitClosureBody e
emitClosureBody (AllocCont ks e) = emitContAlloc ks ++ emitClosureBody e
emitClosureBody (HaltH x) =
  ["    HALT(" ++ emitName x ++ ");"]
emitClosureBody (JumpH k x) =
  ["    JUMP(" ++ emitName k ++ ", " ++ emitName x ++ ");"]
emitClosureBody (CallH f x k) =
  ["    TAILCALL(" ++ emitName f ++ ", " ++ emitName x ++ ", " ++ emitName k ++ ");"]
emitClosureBody (CaseH x k1 k2) =
  ["    CASE(" ++ emitName x ++ ", " ++ emitName k1 ++ ", " ++ emitName k2 ++ ");"]

emitPrimOp :: PrimOp -> String
emitPrimOp (PrimAddInt32 x y) = "prim_addint32(" ++ emitName x ++ ", " ++ emitName y ++ ");"
emitPrimOp (PrimSubInt32 x y) = "prim_subint32(" ++ emitName x ++ ", " ++ emitName y ++ ");"
emitPrimOp (PrimMulInt32 x y) = "prim_mulint32(" ++ emitName x ++ ", " ++ emitName y ++ ");"
emitPrimOp (PrimIsZero32 x) = "prim_iszero32(" ++ emitName x ++ ");"

emitFunAlloc :: [FunAlloc] -> [String]
emitFunAlloc fs =
  map (\ (FunAlloc p d env) -> emitAlloc bindGroup p d env) fs ++
  concatMap (\ (FunAlloc p _ env) -> emitPatch bindGroup p env) fs
  where
    bindGroup :: Set String
    bindGroup = Set.fromList $ map (\ (FunAlloc _ (DeclName f) _) -> f) fs

emitContAlloc :: [ContAlloc] -> [String]
emitContAlloc fs =
  map (\ (ContAlloc p d env) -> emitAlloc bindGroup p d env) fs ++
  concatMap (\ (ContAlloc p _ env) -> emitPatch bindGroup p env) fs
  where
    bindGroup :: Set String
    bindGroup = Set.fromList $ map (\ (ContAlloc _ (DeclName f) _) -> f) fs

-- Names in bindGroup -> NULL
emitAlloc :: Set String -> PlaceName -> DeclName -> EnvAlloc -> String
emitAlloc bindGroup (PlaceName Fun p) d (EnvAlloc xs) =
  "    struct fun *" ++ p ++ " = " ++ "allocate_fun(" ++ intercalate ", " args ++ ");"
  where
    ns = namesForDecl d
    args = [envArg, codeArg, traceArg]
    -- Allocate closure environment here, with NULL for cyclic captures.
    envArg = declAllocName ns ++ "(" ++ intercalate ", " (map allocArg xs) ++ ")"
    allocArg (LocalName x) = if Set.member x bindGroup then "NULL" else x
    allocArg (EnvName x) = x
    codeArg = declCodeName ns
    traceArg = declTraceName ns
emitAlloc bindGroup (PlaceName Cont p) d (EnvAlloc xs) =
  "    struct cont *" ++ p ++ " = " ++ "allocate_cont(" ++ intercalate ", " args ++ ");"
  where
    ns = namesForDecl d
    args = [envArg, codeArg, traceArg]
    -- Allocate closure environment here, with NULL for cyclic captures.
    envArg = declAllocName ns ++ "(" ++ intercalate ", " (map allocArg xs) ++ ")"
    allocArg (LocalName x) = if Set.member x bindGroup then "NULL" else x
    allocArg (EnvName x) = x
    codeArg = declCodeName ns
    traceArg = declTraceName ns
emitAlloc _ (PlaceName Value _) _ _ = error "Values are not allocated through this function."

emitPatch :: Set String -> PlaceName -> EnvAlloc -> [String]
emitPatch bindGroup (PlaceName _ p) (EnvAlloc xs) =
  [p ++ "->env->" ++ x ++ " = " ++ x ++ ";" | LocalName x <- xs, Set.member x bindGroup]

emitPlace :: PlaceName -> String
emitPlace (PlaceName Fun f) = "struct fun *" ++ f
emitPlace (PlaceName Cont k) = "struct cont *" ++ k
emitPlace (PlaceName Value x) = "struct value *" ++ x

-- TODO: Parametrize this by what the name of the environment pointer is.
-- There may be situations where 'env' or 'envp' is the name of a parameter.
emitName :: Name -> String
emitName (LocalName x) = x
emitName (EnvName x) = "env->" ++ x

-- emitFunDecl :: FunDecl -> [String]
-- emitFunDecl (FunDecl FnName [FnName] [CoVar] [TmVar] TmVar CoVar TermH) = _
  -- Env, allocate, trace, code.

