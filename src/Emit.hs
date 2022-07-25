
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
    closureEnvName :: String
  , closureEnvInfo :: String
  , closureAllocName :: String
  , closureTraceName :: String
  , closureCodeName :: String
  , closureEnterName :: String
  }

namesForClosure :: ClosureName -> ClosureNames
namesForClosure (ClosureName f) =
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
  , closureEnterName = "enter_" ++ f
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

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0..]

-- TODO: Build auxiliary structure that contains information necessary to emit
-- thunk types. (provide, not reconstruct)
emitThunkDecl :: ThunkType -> [String]
emitThunkDecl t =
  let ns = namesForThunk t in
  emitThunkType ns t ++
  emitThunkTrace ns t ++
  emitThunkSuspend ns t

emitThunkType :: ThunkNames -> ThunkType -> [String]
emitThunkType ns (ThunkType ss) =
  ["struct " ++ thunkTypeName ns ++ " {"
  ,"    struct thunk header;"
  ,"    struct closure *closure;"] ++
  concat (mapWithIndex mkField ss) ++
  ["};"]
  where
    mkField i ThunkInfoArg =
      ["    type_info arg" ++ show i ++ ";"]
    mkField i (ThunkValueArg s) =
      ["    " ++ emitPlace (Place s (Id ("arg" ++ show i))) ++ ";"
      ,"    " ++ emitInfoPlace (InfoPlace (Id ("info" ++ show i))) ++ ";"]

emitThunkTrace :: ThunkNames -> ThunkType -> [String]
emitThunkTrace ns (ThunkType ss) =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = (struct " ++ thunkTypeName ns ++ " *)next_step;"
  ,"    " ++ emitMarkGray (Id "next") (EnvName (Id "closure")) ClosureInfo ++ ";"] ++
  concat (mapWithIndex traceField ss) ++
  ["}"]
  where
    traceField _ ThunkInfoArg = []
    traceField i (ThunkValueArg _) =
      let arg = EnvName (Id ("arg" ++ show i)) in
      let info = EnvInfo (Id ("info" ++ show i)) in
      ["    " ++ emitMarkGray (Id "next") arg info ++ ";"]

emitThunkSuspend :: ThunkNames -> ThunkType -> [String]
emitThunkSuspend ns (ThunkType ss) =
  ["void " ++ thunkSuspendName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ thunkTypeName ns ++ " *next = realloc(next_step, sizeof(struct " ++ thunkTypeName ns ++ "));"
  ,"    next->header.enter = closure->enter;"
  ,"    next->header.trace = " ++ thunkTraceName ns ++ ";"
  ,"    next->closure = closure;"] ++
  concat (mapWithIndex assignField ss) ++
  ["    next_step = (struct thunk *)next;"
  ,"}"]
  where
    paramList = commaSep ("struct closure *closure" : concat (mapWithIndex makeParam ss))
    makeParam i ThunkInfoArg = ["type_info arg" ++ show i]
    makeParam i (ThunkValueArg s) = case s of
      AllocH _ -> ["struct alloc_header *arg" ++ show i, "type_info info" ++ show i]
      _ -> [emitPlace (Place s (Id ("arg" ++ show i)))]

    assignField i ThunkInfoArg =
      ["    next->arg" ++ show i ++ " = arg" ++ show i ++ ";"]
    assignField i (ThunkValueArg s) =
      ["    next->arg" ++ show i ++ " = arg" ++ show i ++ ";"
      ,"    next->info" ++ show i ++ " = " ++ emitInfo (Id "next") info ++ ";"]
      where
        info = case s of
          AllocH _ -> EnvInfo (Id ("info" ++ show i))
          IntegerH -> Int64Info
          BooleanH -> BoolInfo
          UnitH -> UnitInfo
          SumH -> SumInfo
          ProductH _ _ -> ProductInfo
          ListH _ -> ListInfo
          ClosureH _ -> ClosureInfo

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
  emitEnvDecl ns envd ++
  emitEnvInfo ns envd ++
  emitEnvAlloc ns envd

emitEnvDecl :: ClosureNames -> EnvDecl -> [String]
emitEnvDecl ns (EnvDecl is fs) =
  ["struct " ++ closureEnvName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkInfo is ++
  map mkField fs ++
  ["};"]
  where
    mkInfo i = "    " ++ emitInfoPlace i ++ ";"
    mkField (f, _) = "    " ++ emitPlace f ++ ";"

emitEnvAlloc :: ClosureNames -> EnvDecl -> [String]
-- TODO: What if there is a parameter named 'env'?
-- (Use envName from the ClosureDecl here)
emitEnvAlloc ns (EnvDecl is fs) =
  ["struct " ++ closureEnvName ns ++ " *" ++ closureAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ closureEnvName ns ++ " *env = malloc(sizeof(struct " ++ closureEnvName ns ++ "));"]++
  map assignInfo is ++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(env), " ++ closureEnvInfo ns ++ ");"
  ,"    return env;"
  ,"}"]
  where
    paramList = if null is && null fs then "void" else commaSep params
    params = map emitInfoPlace is ++ map (emitPlace . fst) fs

    assignInfo (InfoPlace aa) = "    env->" ++ show aa ++ " = " ++ show aa ++ ";"
    assignField (Place _ x, _) = "    env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: ClosureNames -> EnvDecl -> [String]
emitEnvInfo ns (EnvDecl _is fs) =
  ["void " ++ closureTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ show envName ++ " = (" ++ envTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"type_info " ++ closureEnvName ns ++ "_info = { " ++ closureTraceName ns ++ ", display_env };"]
  where
    envName = Id "env"
    envTy = "struct " ++ closureEnvName ns ++ " *"
    traceField (Place _ x, i) = "    " ++ emitMarkGray envName (EnvName x) i ++ ";"

emitClosureEnter :: ClosureNames -> ThunkType -> [String]
emitClosureEnter ns ty@(ThunkType ss) =
  ["void " ++ closureEnterName ns ++ "(void) {"
  ,"    " ++ thunkTy ++ "next = (" ++ thunkTy ++ ")next_step;"
  ,"    " ++ envTy ++ "env = (" ++ envTy ++ ")next->closure->env;"
  ,"    " ++ closureCodeName ns ++ "(" ++ commaSep argList ++ ");"
  ,"}"]
  where
    thunkTy = "struct " ++ thunkTypeName (namesForThunk ty) ++ " *"
    envTy = "struct " ++ closureEnvName ns ++ " *"
    argList = "env" : mapWithIndex (\i _ -> "next->arg" ++ show i) ss

emitClosureCode :: ClosureNames -> Id -> [ClosureParam] -> TermH -> [String]
emitClosureCode ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"] ++
  emitClosureBody envName e ++
  ["}"]
  where
    paramList = commaSep (envParam : map emitParam xs)
    envParam = "struct " ++ closureEnvName ns ++ " *" ++ show envName
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
emitClosureBody envp (HaltH x i) =
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
        mkArg _ ThunkInfoArg = error "info args in case (existential ADTs not supported)"
        mkArg argName (ThunkValueArg argSort) =
          asSort argSort (ctorCast ++ "(" ++ emitName envp x ++ ")->" ++ argName)
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

emitAllocGroup :: EnvPtr -> [ClosureAlloc] -> [String]
emitAllocGroup envp closures =
  map (emitAlloc envp) closures ++
  concatMap (\ (ClosureAlloc p d env) -> emitPatch (closureEnvName (namesForClosure d)) p env) closures

emitAlloc :: EnvPtr -> ClosureAlloc -> String
emitAlloc envp (ClosureAlloc p d (EnvAlloc info fields)) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep args ++ ");"
  where
    ns = namesForClosure d
    args = [envArg, traceArg, enterArg]
    envArg = asAlloc (closureAllocName ns ++ "(" ++ commaSep envAllocArgs ++ ")")
    traceArg = closureEnvInfo ns
    enterArg = closureEnterName ns

    -- Recursive/cyclic environment references are initialized to NULL, and
    -- then patched once all the closures have been allocated.
    envAllocArgs = map (emitInfo envp . snd) info ++ map emitAllocArg fields

    emitAllocArg (EnvFreeArg _ x) = emitName envp x
    emitAllocArg (EnvRecArg _ _) = "NULL"

emitPatch :: String -> Place -> EnvAlloc -> [String]
emitPatch envName (Place _ closureId) (EnvAlloc _info fields) =
  concatMap patchField fields
  where
    -- If closure environments had their own Id/Place, this casting would not
    -- be necessary.
    env = "((struct " ++ envName ++ " *)" ++ show closureId ++ "->env)"
    patchField (EnvFreeArg _ _) = []
    patchField (EnvRecArg (Place _ f) (LocalName x)) =
      ["    " ++ env ++ "->" ++ show f ++ " = " ++ show x ++ ";"]
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

