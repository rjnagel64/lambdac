
module Emit (emitProgram) where

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (intercalate)

import qualified Hoist as H
import Hoist

emitProgram :: ([H.TopDecl], TermH) -> [String]
emitProgram (ds, e) = emitFunBody (namesForDecl (DeclName "<entry>")) e

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

-- TODO: Bind groups have to be emitted all at once so that proper ordering can
-- be achieved.
emitFunDecl :: H.FunDecl -> [String]
emitFunDecl (H.FunDecl d envd x k e) =
  emitEnvDecl ns envd ++ emitEnvAlloc ns envd ++ emitEnvTrace ns envd ++ emitFunCode ns x k e
  where
    ns = namesForDecl d

emitEnvDecl :: DeclNames -> EnvDecl -> [String]
emitEnvDecl ns (EnvDecl fs) =
  ["struct " ++ declEnvName ns ++ " {"] ++
  map mkField fs ++
  ["}"]
  where
    mkField (FieldName Fun f) = "    struct fun *" ++ f ++ ";";
    mkField (FieldName Cont k) = "    struct cont *" ++ k ++ ";";
    mkField (FieldName Value x) = "    struct value *" ++ x ++ ";"

emitEnvAlloc :: DeclNames -> EnvDecl -> [String]
emitEnvAlloc ns (EnvDecl fs) =
  ["struct " ++ declEnvName ns ++ " *" ++ declAllocName ns ++ "(" ++ params ++ ") {"] ++
  ["    struct " ++ declEnvName ns ++ " *env = malloc(sizeof(struct " ++ declEnvName ns ++ "));"] ++
  map assignField fs ++
  ["return env;"
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
  ["void " ++ declCodeName ns ++ "(void *envp, " ++ emitPlaceName x ++ ", " ++ emitPlaceName k ++ ") {"
  ,"    struct " ++ declEnvName ns ++ " *env = envp"] ++
  -- TODO: Allocate locals.
  emitFunBody ns e ++
  ["}"]

emitFunBody :: DeclNames -> TermH -> [String]
emitFunBody ns (LetValH x (IntValH i) e) =
  ["    " ++ emitPlaceName x ++ " = allocate_int32(" ++ show i ++");"] ++
  emitFunBody ns e
emitFunBody ns (LetPrimH x p e) =
  ["    " ++ emitPlaceName x ++ " = " ++ emitPrimOp p ++ ";"] ++
  emitFunBody ns e
emitFunBody ns (AllocFun fs e) = emitFunAlloc ns fs ++ emitFunBody ns e
emitFunBody ns (JumpH k x) =
  ["    JUMP(" ++ emitNameOccurrence k ++ ", " ++ emitNameOccurrence x ++ ");"]

emitPrimOp :: PrimOp -> String
emitPrimOp (PrimAddInt32 x y) = "prim_addint32(" ++ emitNameOccurrence x ++ ", " ++ emitNameOccurrence y ++ ");"

emitFunAlloc :: DeclNames -> [FunAlloc] -> [String]
emitFunAlloc ns fs = map emitAlloc fs ++ concatMap emitPatch fs
  where
    bindGroup :: Set String
    bindGroup = Set.fromList $ map (\ (FunAlloc (DeclName f) _) -> f) fs

    -- Names in bindGroup -> NULL
    emitAlloc :: FunAlloc -> String
    emitAlloc (FunAlloc (DeclName f) (EnvAlloc xs)) =
      "    struct fun *" ++ f ++ " = " ++ "allocate_fun(" ++ intercalate ", " args ++ ");"
      where
        args = [envArg, codeArg, traceArg]
        -- Allocate closure environment here, with NULL for cyclic captures.
        envArg = declAllocName ns ++ "(" ++ intercalate ", " (map allocArg xs) ++ ")"
        allocArg (LocalName x) = if Set.member x bindGroup then "NULL" else x
        allocArg (EnvName x) = x
        codeArg = declCodeName ns
        traceArg = declTraceName ns

    -- Assign to each name in the bindGroup
    emitPatch :: FunAlloc -> [String]
    emitPatch (FunAlloc f (EnvAlloc xs)) =
      -- Is the field name the same as the local variable name? I'm not quite
      -- certain. Strange things can happen.
      ["env->" ++ x ++ " = " ++ x ++ ";" | LocalName x <- xs, Set.member x bindGroup]

emitPlaceName :: PlaceName -> String
emitPlaceName (PlaceName Fun f) = "struct fun *" ++ f
emitPlaceName (PlaceName Cont k) = "struct cont *" ++ k
emitPlaceName (PlaceName Value x) = "struct value *" ++ x

-- TODO: Parametrize this by what the name of the environment pointer is.
-- There may be situations where 'env' or 'envp' is the name of a parameter.
emitNameOccurrence :: Name -> String
emitNameOccurrence (LocalName x) = x
emitNameOccurrence (EnvName x) = "env->" ++ x

-- emitFunDecl :: FunDecl -> [String]
-- emitFunDecl (FunDecl FnName [FnName] [CoVar] [TmVar] TmVar CoVar TermH) = _
  -- Env, allocate, trace, code.

