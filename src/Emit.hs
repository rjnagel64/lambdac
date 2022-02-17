
module Emit () where

import CC (TermC(..), CName(..))

newtype CapturedVars = CapturedVars [EnvName]

data FunNames
  = FunNames {
    funEnvName :: String
  , funAllocName :: String
  , funCodeName :: String
  , funTraceName :: String
  }

namesForFun :: FnName -> FunNames
namesForFun (FnName f) =
  FunNames {
    funEnvName = f ++ "_env"
  , funAllocName = "allocate_" ++ f ++ "_env"
  , funCodeName = f ++ "_code"
  , funTraceName = "trace_" ++ f ++ "_env"
  }

emitFunEnv :: FunNames -> CapturedVars -> [String]
emitFunEnv ns (CapturedVars xs) =
  ["struct " ++ funEnvName ns ++ " {"] ++
  map mkField xs ++
  ["}"]
  where
    mkField :: EnvName -> String
    mkField (EnvName CFun f) = "    struct fun *" ++ f ++ ";"
    mkField (EnvName CCont k) = "    struct cont *" ++ k ++ ";"
    mkField (EnvName CValue x) = "    struct value *" ++ x ++ ";"

-- TODO: What if 'env' is the name that gets shadowed? (I.e., the function
-- parameter is named 'env' ot 'envp')
emitFunTrace :: FunNames -> CapturedVars -> [String]
emitFunTrace ns (CapturedVars xs) =
  ["void " ++ funTraceName ns ++ "(void *envp) {"
  ,"    struct " ++ funEnvName ns ++ " *env = envp;"] ++
  map traceField xs ++
  ["}"]
  where
    traceField :: EnvName -> String
    traceField (EnvName CFun f) = "    trace_fun(env->" ++ f ++ ");"
    traceField (EnvName CCont k) = "    trace_cont(env->" ++ k ++ ");"
    traceField (EnvName CValue x) = "    trace_value(env->" ++ x ++ ");"

-- TODO: What if 'env' is the name that gets shadowed? (I.e., the function
-- parameter is named 'env')
emitFunCode :: FunNames -> LocalName -> LocalName -> TermH -> [String]
emitFunCode ns x k e =
  ["void " ++ funCodeName ns ++ "(void *envp, " ++ emitPlaceName x ++ ", " ++ emitPlaceName k ++ ") {"
  ,"    struct " ++ funEnvName ns ++ " *env = envp"] ++
  -- TODO: Allocate locals.
  emitFunBody ns e ++
  ["}"]

emitFunBody :: FunNames -> TermH -> [String]
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

emitFunAlloc :: FunNames -> [FunAlloc] -> [String]
emitFunAlloc ns fs = map emitAlloc fs ++ concatMap emitPatch fs
  where
    -- TODO: These are LocalName, but the actual occurrences in xs are EnvName.
    -- I suppose hoist should distinguish between recursive and non-recursive captures.
    bindGroup :: Set LocalName -- Or Set?
    bindGroup = Set.fromList $ map (\ (FunAlloc f _) -> f) fs

    -- Names in bindGroup -> NULL
    emitAlloc :: FunAlloc -> String
    emitAlloc (FunAlloc f (CapturedVars xs)) =
      -- Environment with bound variables, code pointer, tracing pointer
      emitPlaceName f ++ " = " ++ funAllocName ns ++ "(" ++ _ ++ ");"

    -- Assign to each name in the bindGroup
    emitPatch :: FunAlloc -> [String]
    emitPatch (FunAlloc f (CapturedVars xs)) = concatMap g xs
      where
        -- env->x = x
        -- Or maybe
        -- env->x = x0
        g x = if Set.notMember x bindGroup then [] else [_]

emitPlaceName :: LocalName -> String
emitPlaceName (LocalName CFun f) = "struct fun *" ++ f
emitPlaceName (LocalName CCont k) = "struct cont *" ++ k
emitPlaceName (LocalName CValue x) = "struct value *" ++ x

emitNameOccurrence :: CName -> String
emitNameOccurrence (LocalCName (LocalName _ x)) = x
emitNameOccurrence (EnvCName (EnvName _ x)) = "env->" ++ x

-- emitFunDecl :: FunDecl -> [String]
-- emitFunDecl (FunDecl FnName [FnName] [CoVar] [TmVar] TmVar CoVar TermH) = _
  -- Env, allocate, trace, code.

