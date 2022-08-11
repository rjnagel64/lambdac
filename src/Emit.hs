
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

type EnvPtr = Id

emitProgram :: ([ThunkType], [ClosureDecl], TermH) -> [String]
emitProgram (ts, cs, e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap emitClosureDecl cs ++
  emitEntryPoint e

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

namesForClosure :: ClosureName -> ClosureNames
namesForClosure (ClosureName f) =
  ClosureNames {
    -- These methods (except closureCodeName) are very similar to declaring a
    -- product type, though the trace method is not a proper type info.
    -- (The env is not an alloc_header, and the trace method is not wrapped in
    -- a 'type_info')
    closureEnvName = namesForEnv (ClosureName f)
  , closureCodeName = f ++ "_code"
  , closureEnterName = "enter_" ++ f
  }

namesForEnv :: ClosureName -> EnvNames
namesForEnv (ClosureName f) =
  EnvNames {
    envTypeName = f ++ "_env"
  , envInfoName = f ++ "_env_info"
  , envAllocName = "allocate_" ++ f ++ "_env"
  , envTraceName = "trace_" ++ f ++ "_env"
  }

prologue :: [String]
prologue = ["#include \"rts.h\""]

emitEntryPoint :: TermH -> [String]
emitEntryPoint e =
  ["void program_entry(void) {"] ++
  emitClosureBody (Id "NULL") e ++ -- There is no top-level environment. All names are local.
  ["}"]

data ThunkNames
  = ThunkNames {
    thunkTypeName :: String
  , thunkTraceName :: String
  , thunkSuspendName :: String
  }


namesForThunk :: ThunkType -> ThunkNames
namesForThunk ty =
  ThunkNames {
    thunkTypeName = "thunk_" ++ code
  , thunkTraceName = "trace_" ++ code
  , thunkSuspendName = "suspend_" ++ code
  }
  where
    code = thunkTypeCode ty

typeForSort :: Sort -> String
typeForSort (AllocH _) = "struct alloc_header *"
typeForSort (ClosureH _) = "struct closure *"
typeForSort IntegerH = "struct int64_value *"
typeForSort SumH = "struct sum *"
typeForSort BooleanH = "struct bool_value *"
typeForSort (ProductH _ _) = "struct pair *"
typeForSort UnitH = "struct unit *"
typeForSort (ListH _) = "struct list *"

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort IntegerH x = "AS_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "AS_CLOSURE(" ++ x ++ ")"
asSort SumH x = "AS_SUM(" ++ x ++ ")"
asSort BooleanH x = "AS_BOOL(" ++ x ++ ")"
asSort (ProductH _ _) x = "AS_PAIR(" ++ x ++ ")"
asSort UnitH x = "AS_UNIT(" ++ x ++ ")"
asSort (ListH _s) x = "AS_LIST(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"

emitMarkGray :: EnvPtr -> Name -> Info -> String
emitMarkGray envp x s = "mark_gray(" ++ asAlloc (emitName envp x) ++ ", " ++ emitInfo envp s ++ ")"

emitThunkDecl :: ThunkType -> [String]
emitThunkDecl t =
  let ns = namesForThunk t in
  emitThunkType ns t ++
  emitThunkTrace ns t ++
  emitThunkSuspend ns t

-- TODO: emitThunkType does not need to be specialized
emitThunkType :: ThunkNames -> ThunkType -> [String]
emitThunkType ns (ThunkType ss) =
  ["struct " ++ thunkTypeName ns ++ " {"
  ,"    struct thunk header;"
  ,"    struct args *args;"
  ,"};"]

-- TODO: emitThunkTrace does not need to be specialized
emitThunkTrace :: ThunkNames -> ThunkType -> [String]
emitThunkTrace ns (ThunkType ss) =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    trace_args(next->args);"
  ,"}"]

emitThunkSuspend :: ThunkNames -> ThunkType -> [String]
emitThunkSuspend ns (ThunkType ss) =
  ["void " ++ thunkSuspendName ns ++ "(" ++ commaSep paramList ++ ") {"
  ,"    next_closure = closure;"
  ,"    struct " ++ thunkTypeName ns ++ " *next = realloc(next_step, sizeof(struct " ++ thunkTypeName ns ++ "));"
  ,"    next->header.enter = closure->enter;"
  ,"    next->header.trace = " ++ thunkTraceName ns ++ ";"
  ,"    next->args = make_args(" ++ show numValues ++ ", " ++ show numInfos ++ ");"] ++
  assignFields 0 0 ss ++
  ["    next_step = (struct thunk *)next;"
  ,"}"]
  where
    paramList = "struct closure *closure" : makeParams 0 0 ss
    (numValues, numInfos) = countParams 0 0 ss
    
    countParams :: Int -> Int -> [ThunkArg] -> (Int, Int)
    countParams i j [] = (i, j)
    countParams i j (ThunkInfoArg : ss') = countParams i (j+1) ss'
    countParams i j (ThunkValueArg _ : ss') = countParams (i+1) j ss'

    makeParams :: Int -> Int -> [ThunkArg] -> [String]
    makeParams i j (ThunkInfoArg : ss') =
      ("type_info info" ++ show j) :
      makeParams i (j+1) ss'
    makeParams i j (ThunkValueArg (AllocH _) : ss') =
      ("struct alloc_header *arg" ++ show i) :
      ("type_info arginfo" ++ show i) :
      makeParams (i+1) j ss'
    makeParams i j (ThunkValueArg s : ss') =
      emitPlace (Place s (Id ("arg" ++ show i))) :
      makeParams (i+1) j ss'
    makeParams _ _ [] = []

    assignFields :: Int -> Int -> [ThunkArg] -> [String]
    assignFields i j (ThunkInfoArg : ss') =
      ("    next->args->infos[" ++ show j ++ "] = info" ++ show j ++ ";") :
      assignFields i (j+1) ss'
    assignFields i j (ThunkValueArg s : ss') =
      ("    next->args->values[" ++ show i ++ "].alloc = " ++ asAlloc ("arg" ++ show i) ++ ";") :
      ("    next->args->values[" ++ show i ++ "].info = " ++ emitInfo (Id "NULL") info ++ ";") :
      assignFields (i+1) j ss'
      where
        info = case s of
          AllocH _ -> LocalInfo (Id ("arginfo" ++ show i))
          IntegerH -> Int64Info
          BooleanH -> BoolInfo
          UnitH -> UnitInfo
          SumH -> SumInfo
          ProductH _ _ -> ProductInfo
          ListH _ -> ListInfo
          ClosureH _ -> ClosureInfo
    assignFields _ _ [] = []

emitClosureDecl :: H.ClosureDecl -> [String]
emitClosureDecl (H.ClosureDecl d (envName, envd) params e) =
  emitClosureEnv ns envd ++
  emitClosureCode ns envName params e ++
  emitClosureEnter ns ty
  where
    ns = namesForClosure d
    -- TODO: It's a bit inelegant to re-infer the thunk type here.
    ty = ThunkType (map f params)
    f (TypeParam _) = ThunkInfoArg
    f (PlaceParam p) = ThunkValueArg (placeSort p)

emitClosureEnv :: ClosureNames -> EnvDecl -> [String]
emitClosureEnv ns envd =
  let ns' = closureEnvName ns in
  emitEnvDecl ns' envd ++
  emitEnvInfo ns' envd ++
  emitEnvAlloc ns' envd

emitEnvDecl :: EnvNames -> EnvDecl -> [String]
emitEnvDecl ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkInfo is ++
  map mkField fs ++
  ["};"]
  where
    mkInfo i = "    " ++ emitInfoPlace i ++ ";"
    mkField (f, _) = "    " ++ emitPlace f ++ ";"

emitEnvAlloc :: EnvNames -> EnvDecl -> [String]
emitEnvAlloc ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " *" ++ envAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ envTypeName ns ++ " *_env = malloc(sizeof(struct " ++ envTypeName ns ++ "));"]++
  map assignInfo is ++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(_env), " ++ envInfoName ns ++ ");"
  ,"    return _env;"
  ,"}"]
  where
    paramList = if null is && null fs then "void" else commaSep params
    params = map emitInfoPlace is ++ map (emitPlace . fst) fs

    assignInfo (InfoPlace aa) = "    _env->" ++ show aa ++ " = " ++ show aa ++ ";"
    assignField (Place _ x, _) = "    _env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: EnvNames -> EnvDecl -> [String]
emitEnvInfo ns (EnvDecl _is fs) =
  ["void " ++ envTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ show envName ++ " = (" ++ envTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"type_info " ++ envInfoName ns ++ " = { " ++ envTraceName ns ++ ", display_env };"]
  where
    envName = Id "env"
    envTy = "struct " ++ envTypeName ns ++ " *"
    traceField (Place _ x, i) = "    " ++ emitMarkGray envName (EnvName x) i ++ ";"

emitClosureEnter :: ClosureNames -> ThunkType -> [String]
emitClosureEnter ns ty@(ThunkType ss) =
  ["void " ++ closureEnterName ns ++ "(void) {"
  ,"    " ++ thunkTy ++ "next = (" ++ thunkTy ++ ")next_step;"
  ,"    " ++ envTy ++ "env = (" ++ envTy ++ ")next_closure->env;"
  ,"    " ++ closureCodeName ns ++ "(" ++ commaSep argList ++ ");"
  ,"}"]
  where
    thunkTy = "struct " ++ thunkTypeName (namesForThunk ty) ++ " *"
    envTy = "struct " ++ envTypeName (closureEnvName ns) ++ " *"
    argList = "env" : makeArgList 0 0 ss
    makeArgList :: Int -> Int -> [ThunkArg] -> [String]
    makeArgList i j (ThunkInfoArg : ss') = ("next->args->infos[" ++ show j ++ "]") : makeArgList i (j+1) ss'
    makeArgList i j (ThunkValueArg s : ss') = asSort s ("next->args->values[" ++ show i ++ "].alloc") : makeArgList (i+1) j ss'
    makeArgList _ _ [] = []

emitClosureCode :: ClosureNames -> Id -> [ClosureParam] -> TermH -> [String]
emitClosureCode ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"] ++
  emitClosureBody envName e ++
  ["}"]
  where
    paramList = commaSep (envParam : map emitParam xs)
    envParam = "struct " ++ envTypeName (closureEnvName ns) ++ " *" ++ show envName
    emitParam (TypeParam i) = emitInfoPlace i
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
emitClosureBody envp (HaltH _s x i) =
  ["    halt_with(" ++ asAlloc (emitName envp x) ++ ", " ++ emitInfo envp i ++ ");"]
emitClosureBody envp (OpenH c ty args) =
  [emitSuspend envp c ty args]
emitClosureBody envp (CaseH x kind ks) =
  emitCase kind envp x ks

emitSuspend :: EnvPtr -> Name -> ThunkType -> [ClosureArg] -> String
emitSuspend envp cl ty@(ThunkType ss) xs = "    " ++ method ++ "(" ++ commaSep args ++ ");"
  where
    method = thunkSuspendName (namesForThunk ty)
    args = emitName envp cl : zipWith makeArg ss xs

    makeArg ThunkInfoArg (TypeArg i) = emitInfo envp i
    makeArg (ThunkValueArg (AllocH _)) (OpaqueArg y i) = emitName envp y ++ ", " ++ emitInfo envp i
    makeArg (ThunkValueArg _) (OpaqueArg _ _) =
      error "only 'alloc' thunk args should be passed as opaque values"
    makeArg (ThunkValueArg (AllocH _)) (ValueArg _) =
      error "'alloc' thunk args should be opaque values"
    makeArg (ThunkValueArg _) (ValueArg y) = emitName envp y
    makeArg _ _ = error "calling convention mismatch: type/value param paired with value/type arg"


emitCase :: CaseKind -> EnvPtr -> Name -> [Name] -> [String]
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
        args = emitName envp k : map mkArg argNames
        mkArg (argName, argSort) =
          asSort argSort (ctorCast ++ "(" ++ emitName envp x ++ ")->" ++ argName)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

data BranchInfo
  -- How to downcast to the constructor, what thunk type to suspend with, and
  -- the name/sort of each argument to extract.
  = BranchInfo String ThunkType [(String, Sort)]

caseInfoTable :: CaseKind -> [BranchInfo]
caseInfoTable CaseBool =
  [ BranchInfo "AS_BOOL_FALSE" (ThunkType []) []
  , BranchInfo "AS_BOOL_TRUE" (ThunkType []) []
  ]
caseInfoTable (CaseSum t s) =
  [ BranchInfo "AS_SUM_INL" (ThunkType [ThunkValueArg t]) [("payload", t)]
  , BranchInfo "AS_SUM_INR" (ThunkType [ThunkValueArg s]) [("payload", s)]
  ]
caseInfoTable (CaseList t) =
  [ BranchInfo "AS_LIST_NIL" (ThunkType []) []
  , BranchInfo "AS_LIST_CONS" consThunkTy [("head", t), ("tail", ListH t)]
  ]
  where consThunkTy = ThunkType [ThunkValueArg t, ThunkValueArg (ListH t)]

emitValueAlloc :: EnvPtr -> ValueH -> String
emitValueAlloc _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc _ (BoolH True) = "allocate_true()"
emitValueAlloc _ (BoolH False) = "allocate_false()"
emitValueAlloc envp (PairH s1 s2 x y) =
  "allocate_pair(" ++ emitInfo envp s1 ++ ", " ++ emitInfo envp s2 ++ ", " ++ asAlloc (emitName envp x) ++ ", " ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ NilH = "allocate_unit()"
emitValueAlloc envp (InlH s y) =
  "allocate_inl(" ++ asAlloc (emitName envp y) ++ ", " ++ emitInfo envp s ++ ")"
emitValueAlloc envp (InrH s y) =
  "allocate_inr(" ++ asAlloc (emitName envp y) ++ ", " ++ emitInfo envp s ++ ")"
emitValueAlloc _ ListNilH = "allocate_list_nil()"
emitValueAlloc envp (ListConsH s x xs) =
  "allocate_list_cons(" ++ asAlloc (emitName envp x) ++ ", " ++ emitInfo envp s ++ ", " ++ emitName envp xs ++ ")"

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

-- | Allocate a group of (mutually recursive) closures.
--
-- This is a three-step process.
-- - First, each closure's environment is allocated. Cyclic references are
--   initialized with @NULL@.
-- - Second, the closures are allocated using the environments from step 1.
-- - Third, the @NULL@s in the environments are patched to refer to the
--   freshly-allocated closures.
emitAllocGroup :: EnvPtr -> [ClosureAlloc] -> [String]
emitAllocGroup envp closures =
  map (allocEnv envp) closures ++
  map allocClosure closures ++
  concatMap patchEnv closures

allocEnv :: EnvPtr -> ClosureAlloc -> String
allocEnv envp (ClosureAlloc _p d envPlace (EnvAlloc info fields)) =
  "    struct " ++ envTypeName ns' ++ " *" ++ show envPlace ++ " = " ++ call ++ ";"
  where
    ns' = closureEnvName (namesForClosure d)

    call = envAllocName ns' ++ "(" ++ commaSep args ++ ")"
    args = map (emitInfo envp . snd) info ++ map emitAllocArg fields
    emitAllocArg (EnvFreeArg _ x) = emitName envp x
    emitAllocArg (EnvRecArg _ _) = "NULL"

allocClosure :: ClosureAlloc -> String
allocClosure (ClosureAlloc p d envPlace _env) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep args ++ ");"
  where
    ns = namesForClosure d
    ns' = closureEnvName ns
    args = [envArg, traceArg, enterArg]
    envArg = asAlloc (show envPlace)
    traceArg = envInfoName ns'
    enterArg = closureEnterName ns

patchEnv :: ClosureAlloc -> [String]
patchEnv (ClosureAlloc _ _ envPlace (EnvAlloc _info fields)) = concatMap patchField fields
  where
    patchField (EnvFreeArg _ _) = []
    patchField (EnvRecArg (Place _ f) (LocalName x)) =
      ["    " ++ show envPlace ++ "->" ++ show f ++ " = " ++ show x ++ ";"]
    -- Patching recursive closures should only ever involve local names.
    -- Additionally, we do not have access to an environment pointer in this function.
    patchField (EnvRecArg _ (EnvName _)) = []

emitInfoPlace :: InfoPlace -> String
emitInfoPlace (InfoPlace i) = "type_info " ++ show i

emitPlace :: Place -> String
emitPlace (Place s x) = typeForSort s ++ show x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = show x
emitName envp (EnvName x) = show envp ++ "->" ++ show x

emitInfo :: EnvPtr -> Info -> String
emitInfo _ (LocalInfo aa) = show aa
emitInfo envp (EnvInfo aa) = show envp ++ "->" ++ show aa
emitInfo _ Int64Info = "int64_value_info"
emitInfo _ BoolInfo = "bool_value_info"
emitInfo _ UnitInfo = "unit_info"
emitInfo _ SumInfo = "sum_info"
emitInfo _ ProductInfo = "pair_info"
emitInfo _ ClosureInfo = "closure_info"
emitInfo _ ListInfo = "list_info"

