
module Emit
    ( emitProgram

    -- , demoProgram -- Only for testing
    ) where

import Data.Function (on)
import Data.List (intercalate, intersperse)
import Data.Maybe (mapMaybe)
import Data.Traversable (mapAccumL)

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Hoist.IR

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
type Line = String

-- Associate closures in the local environment with their calling conventions.
-- (Split into two parts, because of local declarations vs. declarations from
-- the closure env)
--
-- (Alternately, I could have 'Map Name ThunkType'. Hmm.)
data ThunkEnv = ThunkEnv (Map Name ThunkType)

lookupThunkTy :: ThunkEnv -> Name -> ThunkType
lookupThunkTy (ThunkEnv env) x = case Map.lookup x env of
  Nothing -> error ("missing thunk type for name " ++ show x)
  Just ty -> ty


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

namesForClosure :: CodeLabel -> ClosureNames
namesForClosure (CodeLabel f) =
  ClosureNames {
    closureEnvName = namesForEnv (CodeLabel f)
  , closureCodeName = f ++ "_code"
  , closureEnterName = "enter_" ++ f
  }

namesForEnv :: CodeLabel -> EnvNames
namesForEnv (CodeLabel f) =
  EnvNames {
    envTypeName = f ++ "_env"
  , envInfoName = f ++ "_env_info"
  , envAllocName = "allocate_" ++ f ++ "_env"
  , envTraceName = "trace_" ++ f ++ "_env"
  }


-- | A thunk type is a calling convention for closures: the set of arguments
-- that must be provided to open it. This information is used to generate
-- trampolined tail calls.
--
-- Because 'ThunkType' is mostly concerned with the call site, it does not have
-- a binding structure. (Or does it?)
data ThunkType = ThunkType { thunkArgs :: [ThunkArg] }

data ThunkArg
  = ThunkValueArg Sort
  | ThunkInfoArg

instance Eq ThunkType where (==) = (==) `on` thunkTypeCode
instance Ord ThunkType where compare = compare `on` thunkTypeCode

-- | Construct a thunk type from a closure telescope.
teleThunkType :: ClosureTele -> ThunkType
teleThunkType (ClosureTele ss) = ThunkType (map f ss)
  where
    f (ValueTele s) = ThunkValueArg s
    f (TypeTele aa k) = ThunkInfoArg -- Hmm. type args aren't really info args, though.

thunkTypeCode :: ThunkType -> String
thunkTypeCode (ThunkType ts) = map argcode ts
  where
    argcode ThunkInfoArg = 'I'
    argcode (ThunkValueArg s) = tycode s
    tycode :: Sort -> Char
    tycode IntegerH = 'V'
    tycode BooleanH = 'B'
    tycode StringH = 'T'
    tycode UnitH = 'U'
    -- In C, polymorphic types are represented uniformly.
    -- For example, 'list int64' and 'list (aa * bool)' are both represented
    -- using a 'struct list_val *' value. Therefore, when encoding a thunk type
    -- (that is, summarizing a closure's calling convention), we only need to
    -- mention the outermost constructor.
    tycode (ClosureH _) = 'C'
    tycode (AllocH _) = 'A'
    tycode (ListH _) = 'L'
    tycode (ProductH _ _) = 'Q'
    tycode (SumH _ _) = 'S'

data ThunkNames
  = ThunkNames {
    thunkTypeName :: String
  , thunkArgsName :: String
  , thunkTraceName :: String
  , thunkSuspendName :: String
  }

namesForThunk :: ThunkType -> ThunkNames
namesForThunk ty =
  ThunkNames {
    thunkTypeName = "thunk_" ++ code
  , thunkArgsName = "args_" ++ code
  , thunkTraceName = "trace_args_" ++ code
  , thunkSuspendName = "suspend_" ++ code
  }
  where
    code = thunkTypeCode ty


typeForSort :: Sort -> String
typeForSort (AllocH _) = "struct alloc_header *"
typeForSort (ClosureH _) = "struct closure *"
typeForSort IntegerH = "struct int64_value *"
typeForSort StringH = "struct string_value *"
typeForSort BooleanH = "struct vbool *"
typeForSort (ProductH _ _) = "struct pair *"
typeForSort (SumH _ _) = "struct sum *"
typeForSort UnitH = "struct unit *"
typeForSort (ListH _) = "struct list *"

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort IntegerH x = "CAST_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "CAST_CLOSURE(" ++ x ++ ")"
asSort StringH x = "CAST_STRING(" ++ x ++ ")"
asSort BooleanH x = "CAST_bool(" ++ x ++ ")"
asSort (ProductH _ _) x = "CAST_PAIR(" ++ x ++ ")"
asSort (SumH _ _) x = "CAST_sum(" ++ x ++ ")"
asSort UnitH x = "CAST_UNIT(" ++ x ++ ")"
asSort (ListH _s) x = "CAST_list(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"


-- | Compute the thunk type of a closure declaration.
codeDeclType :: CodeDecl -> ThunkType
codeDeclType decl = teleThunkType (codeDeclTele decl)

-- TODO: collectThunkTypes overapproximates the set of thunk types needed by a program.
-- This bloats the output substantially as program complexity increases.
-- Instead, I should only record the thunk types I actually use.
--
-- (I believe this means traversing the program and counting each OpenH construct)
collectThunkTypes :: [CodeDecl] -> Set ThunkType
collectThunkTypes cs = foldMap closureThunkTypes cs
  where
    closureThunkTypes :: CodeDecl -> Set ThunkType
    closureThunkTypes cd@(CodeDecl _ _ params _) = Set.insert ty (foldMap paramThunkTypes params)
      where ty = codeDeclType cd

    paramThunkTypes :: ClosureParam -> Set ThunkType
    paramThunkTypes (TypeParam _ _) = Set.empty
    paramThunkTypes (PlaceParam p) = thunkTypesOf (placeSort p)

    thunkTypesOf :: Sort -> Set ThunkType
    thunkTypesOf (AllocH _) = Set.empty
    thunkTypesOf IntegerH = Set.empty
    thunkTypesOf BooleanH = Set.empty
    thunkTypesOf StringH = Set.empty
    thunkTypesOf UnitH = Set.empty
    thunkTypesOf (ClosureH tele) = Set.insert (teleThunkType tele) (teleThunkTypes tele)
    thunkTypesOf (ProductH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (SumH t1 t2) = thunkTypesOf t1 <> thunkTypesOf t2
    thunkTypesOf (ListH t) = thunkTypesOf t

    teleThunkTypes :: ClosureTele -> Set ThunkType
    -- We are looking for thunk types, so scoping doesn't matter and foldMap is
    -- fine.
    teleThunkTypes (ClosureTele ss) = foldMap entryThunkTypes ss

    entryThunkTypes :: TeleEntry -> Set ThunkType
    entryThunkTypes (ValueTele s) = thunkTypesOf s
    entryThunkTypes (TypeTele aa k) = Set.empty


type DataEnv = Map TyCon DataDesc

emitProgram :: Program -> [Line]
emitProgram (Program ds e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concat (snd (mapAccumL emitDecl dataEnv ds)) ++
  emitEntryPoint e
  where
    ts = Set.toList $ collectThunkTypes [cd | DeclCode cd <- ds]
    dataEnv = Map.empty

prologue :: [Line]
prologue = ["#include \"rts.h\""]

emitDecl :: DataEnv -> Decl -> (DataEnv, [Line])
emitDecl denv (DeclCode cd) = (denv, emitClosureDecl denv cd)
emitDecl denv (DeclData dd) = let denv' = denv in (denv', emitDataDecl denv dd)

emitEntryPoint :: TermH -> [Line]
emitEntryPoint e =
  ["void program_entry(void) {"] ++
  emitTerm thunkEnv envp e ++
  ["}"]
  where
    -- There is no environment pointer at the top level, because we are not in a closure.
    envp = Id "NULL"
    -- Likewise, there are no fields and no local variables in the environment.
    thunkEnv = ThunkEnv Map.empty


-- Hmm. This should probably be more like a State ClosureSig than a Reader ClosureSig,
-- but I've been lax about the ordering of top-level closures, I think.
emitThunkDecl :: ThunkType -> [Line]
emitThunkDecl t =
  emitThunkArgs ns t ++
  emitThunkTrace ns t ++
  emitThunkSuspend ns t
  where ns = namesForThunk t

foldThunk :: (Int -> Sort -> b) -> ThunkType -> [b]
foldThunk consValue ty = go 0 (thunkArgs ty)
  where
    go _ [] = []
    go i (ThunkValueArg s : ss) = consValue i s : go (i+1) ss
    go i (ThunkInfoArg : ss) = go i ss

emitThunkArgs :: ThunkNames -> ThunkType -> [Line]
emitThunkArgs ns ty =
  ["struct " ++ thunkArgsName ns ++ " {"
  ,"    struct closure *closure;"] ++
  declareFields ty ++
  ["};"]
  where
    declareFields = foldThunk consValue
      where
        consValue i s =
          let p = Place s (Id ("arg" ++ show i)) in
          "    " ++ emitPlace p ++ ";"

emitThunkTrace :: ThunkNames -> ThunkType -> [Line]
emitThunkTrace ns ty =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    mark_gray(AS_ALLOC(args->closure));"] ++
  body ++
  ["}"]
  where
    argsTy = "struct " ++ thunkArgsName ns ++ " *"
    body = foldThunk consValue ty
      where consValue i _ = "    mark_gray(" ++ asAlloc ("args->arg" ++ show i) ++ ");"

emitThunkSuspend :: ThunkNames -> ThunkType -> [Line]
emitThunkSuspend ns ty =
  ["void " ++ thunkSuspendName ns ++ "(" ++ commaSep paramList ++ ") {"
  ,"    reserve_args(sizeof(struct " ++ thunkArgsName ns ++ "));"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    args->closure = closure;"]++
  assignFields ty ++
  ["    set_next(closure->enter, " ++ thunkTraceName ns ++ ");"
  ,"}"]
  where
    argsTy = "struct " ++ thunkArgsName ns ++ " *"
    paramList = "struct closure *closure" : foldThunk consValue ty
      where
        consValue i s@(AllocH _) =
          let p = Place s (Id ("arg" ++ show i)) in
          emitPlace p
        consValue i s = let p = Place s (Id ("arg" ++ show i)) in emitPlace p
    assignFields = foldThunk consValue
      where
        consValue i _ =
          let arg = "arg" ++ show i in
          "    args->" ++ arg ++ " = " ++ arg ++ ";"


emitDataDecl :: DataEnv -> DataDecl -> [Line]
emitDataDecl denv dd@(DataDecl tc params ctors) =
  let desc = dataDesc dd (map (AllocH . fst) params) in
  emitDataStruct dd ++
  concatMap (emitCtorDecl desc) ctors

emitDataStruct :: DataDecl -> [Line]
emitDataStruct (DataDecl tc _ _) =
  ["struct " ++ show tc ++ " {"
  ,"    struct alloc_header header;"
  ,"    uint32_t discriminant;"
  ,"};"
  ,"#define CAST_" ++ show tc ++ "(v) ((struct " ++ show tc ++ " *)(v))"]

emitCtorDecl :: DataDesc -> CtorDecl -> [Line]
emitCtorDecl desc cd =
  emitCtorStruct desc cd ++
  emitCtorInfo desc cd ++
  emitCtorAllocate desc cd

emitCtorStruct :: DataDesc -> CtorDecl -> [Line]
emitCtorStruct desc (CtorDecl c args) =
  let tc = dataName desc in
  let ctorId = tc ++ "_" ++ show c in
  ["struct " ++ ctorId ++ " {"
  ,"    struct " ++ tc ++ " header;"] ++
  map makeField args ++
  ["};"
  ,"#define CAST_" ++ ctorId ++ "(v) ((struct " ++ ctorId ++ " *)(v))"]
  where makeField (x, s) = "    " ++ emitPlace (Place s x) ++ ";"

emitCtorInfo :: DataDesc -> CtorDecl -> [Line]
emitCtorInfo desc (CtorDecl c args) =
  -- Hmm. May need DataNames and CtorNames
  let tc = dataName desc in
  let ctorId = tc ++ "_" ++ show c in
  let ctorCast = "CAST_" ++ ctorId in
  ["void trace_" ++ ctorId ++ "(struct alloc_header *alloc) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ "(alloc);"] ++
  map traceField args ++
  ["}"
  ,"void display_" ++ ctorId ++ "(struct alloc_header *alloc, struct string_buf *sb) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ "(alloc);"
  ,"    string_buf_push(sb, \"" ++ show c ++ "\");"
  ,"    string_buf_push(sb, \"(\");"] ++
  intersperse "string_buf_push(sb, \", \");" (map displayField args) ++
  ["    string_buf_push(sb, \")\");"
  ,"}"
  ,"const type_info " ++ ctorId ++ "_info = { trace_" ++ ctorId ++ ", display_" ++ ctorId ++ " };"]
  where
    traceField (x, s) = "    mark_gray(ctor->" ++ show x ++ ");"
    displayField (x, s) = "    AS_ALLOC(ctor->" ++ show x ++ ")->info->display(ctor->" ++ show x ++ ", sb);"

emitCtorAllocate :: DataDesc -> CtorDecl -> [Line]
emitCtorAllocate desc cd@(CtorDecl c args) =
  let tc = dataName desc in
  let ctorId = tc ++ "_" ++ show c in
  ["struct " ++ tc ++ " *allocate_" ++ ctorId ++ "(" ++ commaSep params ++ ") {"
  ,"    struct " ++ ctorId ++ " *ctor = malloc(sizeof(struct " ++ ctorId ++ "));"
  ,"    ctor->header.discriminant = " ++ show (ctorDiscriminant (dataCtors desc Map.! c)) ++ ";"] ++
  map assignField args ++
  ["    cons_new_alloc(" ++ asAlloc "ctor" ++ ", &" ++ ctorId ++ "_info);"
  ,"    return " ++ dataUpcast desc ++ "(ctor);"
  ,"}"]
  where
    params = [emitPlace (Place s x) | (x, s) <- args]
    assignField (x, s) = "    ctor->" ++ show x ++ " = " ++ show x ++ ";"

-- demoProgram :: Program
-- demoProgram = Program [DeclData dd] e
--   where
--     dd = DataDecl tc [(aa, Star)] [CtorDecl (Ctor "nothing") [], CtorDecl (Ctor "just") [(Id "val", AllocH aa)]]
--     e = LetValH (Place UnitH x) NilH (HaltH UnitH (LocalName x))
--     x = Id "x"
--     aa = TyVar (Id "aa")
--     tc = TyCon "maybe"


emitClosureDecl :: DataEnv -> CodeDecl -> [Line]
emitClosureDecl denv cd@(CodeDecl d (envName, envd@(EnvDecl _ places)) params e) =
  emitClosureEnv cns envd ++
  emitClosureCode thunkEnv cns envName params e ++
  emitClosureEnter tns cns ty
  where
    cns = namesForClosure d
    tns = namesForThunk ty
    ty = codeDeclType cd

    -- The thunkEnv maps variables to their thunk type, so that the correct
    -- suspend method can be picked in emitSuspend
    thunkEnv = ThunkEnv (foldr addParam (foldr addPlace Map.empty places) params) 
    addParam (PlaceParam (Place (ClosureH tele) x)) acc =
      Map.insert (LocalName x) (teleThunkType tele) acc
    addParam (PlaceParam _) acc = acc
    addParam (TypeParam _ _) acc = acc

    addPlace (Place (ClosureH tele) x) acc =
      Map.insert (EnvName x) (teleThunkType tele) acc
    addPlace (Place _ _) acc = acc

emitClosureEnv :: ClosureNames -> EnvDecl -> [Line]
emitClosureEnv ns envd =
  let ns' = closureEnvName ns in
  emitEnvDecl ns' envd ++
  emitEnvInfo ns' envd ++
  emitEnvAlloc ns' envd

emitEnvDecl :: EnvNames -> EnvDecl -> [Line]
emitEnvDecl ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkField fs ++
  ["};"]
  where
    mkField f = "    " ++ emitPlace f ++ ";"

emitEnvAlloc :: EnvNames -> EnvDecl -> [Line]
emitEnvAlloc ns (EnvDecl is fs) =
  ["struct " ++ envTypeName ns ++ " *" ++ envAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ envTypeName ns ++ " *_env = malloc(sizeof(struct " ++ envTypeName ns ++ "));"]++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(_env), &" ++ envInfoName ns ++ ");"
  ,"    return _env;"
  ,"}"]
  where
    paramList = if null params then "void" else commaSep params
    params = map emitPlace fs
    assignField (Place _ x) = "    _env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: EnvNames -> EnvDecl -> [Line]
emitEnvInfo ns (EnvDecl is fs) =
  ["void " ++ envTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ show envName ++ " = (" ++ envTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"const type_info " ++ envInfoName ns ++ " = { " ++ envTraceName ns ++ ", display_env };"]
  where
    envName = Id "env"
    envTy = "struct " ++ envTypeName ns ++ " *"
    traceField (Place _ x) =
      let field = asAlloc (emitName envName (EnvName x)) in
      "    mark_gray(" ++ field ++ ");"

emitClosureEnter :: ThunkNames -> ClosureNames -> ThunkType -> [Line]
emitClosureEnter tns cns ty =
  ["void " ++ closureEnterName cns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    " ++ envTy ++ "env = (" ++ envTy ++ ")args->closure->env;"
  ,"    " ++ closureCodeName cns ++ "(" ++ commaSep argList ++ ");"
  ,"}"]
  where
    argsTy = "struct " ++ thunkArgsName tns ++ " *"
    envTy = "struct " ++ envTypeName (closureEnvName cns) ++ " *"
    argList = "env" : foldThunk consValue ty
      where consValue i _ = "args->arg" ++ show i

-- Hmm. emitEntryPoint and emitClosureCode are nearly identical, save for the
-- environment pointer.
emitClosureCode :: ThunkEnv -> ClosureNames -> Id -> [ClosureParam] -> TermH -> [Line]
emitClosureCode tenv ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"] ++
  emitTerm tenv envName e ++
  ["}"]
  where
    paramList = commaSep (envParam : mapMaybe emitParam xs)
    envParam = "struct " ++ envTypeName (closureEnvName ns) ++ " *" ++ show envName
    emitParam (TypeParam _ _) = Nothing
    emitParam (PlaceParam p) = Just (emitPlace p)


emitTerm :: ThunkEnv -> EnvPtr -> TermH -> [Line]
emitTerm tenv envp (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValueAlloc envp (placeSort x) v ++ ";"] ++
  emitTerm tenv envp e
emitTerm tenv envp (LetProjectH x y ProjectFst e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->fst") ++ ";"] ++
  emitTerm tenv envp e
emitTerm tenv envp (LetProjectH x y ProjectSnd e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->snd") ++ ";"] ++
  emitTerm tenv envp e
emitTerm tenv envp (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp envp p ++ ";"] ++
  emitTerm tenv envp e
emitTerm tenv envp (AllocClosure cs e) =
  emitClosureGroup envp cs ++
  let tenv' = extendThunkEnv tenv cs in
  emitTerm tenv' envp e
emitTerm _ envp (HaltH _ x) =
  ["    halt_with(" ++ asAlloc (emitName envp x) ++ ");"]
emitTerm tenv envp (OpenH c args) =
  [emitSuspend tenv envp c args]
emitTerm _ envp (CaseH x kind ks) =
  emitCase kind envp x ks

emitSuspend :: ThunkEnv -> EnvPtr -> Name -> [ClosureArg] -> Line
emitSuspend tenv envp cl xs =
  "    " ++ method ++ "(" ++ commaSep args ++ ");"
  where
    ty = lookupThunkTy tenv cl
    method = thunkSuspendName (namesForThunk ty)
    args = emitName envp cl : mapMaybe makeArg (zip (thunkArgs ty) xs)

    makeArg (ThunkInfoArg, TypeArg i) = Nothing
    makeArg (ThunkValueArg _, ValueArg y) = Just (emitName envp y)
    makeArg _ = error "calling convention mismatch: type/value param paired with value/type arg"


emitCase :: TyConApp -> EnvPtr -> Name -> [(Ctor, Name)] -> [Line]
emitCase kind envp x branches =
  ["    switch (" ++ emitName envp x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch branches ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    tab = dataCtors (dataDescTable kind)

    emitCaseBranch :: (Ctor, Name) -> [String]
    emitCaseBranch (ctor, k) =
      let
        desc = tab Map.! ctor
        method = thunkSuspendName (namesForThunk (ctorThunkType desc))
        ctorVal = ctorDowncast desc ++ "(" ++ emitName envp x ++ ")"
        args = emitName envp k : map mkArg (ctorArgCasts desc)
        mkArg (argName, Nothing) = ctorVal ++ "->" ++ argName
        mkArg (argName, Just argSort) = asSort argSort (ctorVal ++ "->" ++ argName)
      in
        ["    case " ++ show (ctorDiscriminant desc) ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

emitValueAlloc :: EnvPtr -> Sort -> ValueH -> String
emitValueAlloc _ _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc _ _ (StringValH s) = "allocate_string(" ++ show s ++ ")"
emitValueAlloc envp _ (PairH x y) =
  "allocate_pair(" ++ asAlloc (emitName envp x) ++ ", " ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ _ NilH = "allocate_unit()"
emitValueAlloc envp ty (CtorAppH capp) =
  case asTyConApp ty of
    Nothing -> error "not a constructed type"
    Just kind -> emitCtorAlloc envp kind capp

emitCtorAlloc :: EnvPtr -> TyConApp -> CtorAppH -> String
emitCtorAlloc envp kind capp = ctorAllocate desc ++ "(" ++ commaSep args' ++ ")"
  where
    desc = dataCtors (dataDescTable kind) Map.! ctorName
    (ctorName, args) = case capp of
      BoolH True -> (Ctor "true", [])
      BoolH False -> (Ctor "false", [])
      InlH x -> (Ctor "inl", [x])
      InrH x -> (Ctor "inr", [x])
      ListNilH -> (Ctor "nil", [])
      ListConsH x xs -> (Ctor "cons", [x, xs])
    args' = zipWith makeArg args (ctorArgCasts desc)
    makeArg x (_, Nothing) = emitName envp x
    makeArg x (_, Just _) = asAlloc (emitName envp x)

-- Hmm. Consider 'Id' instead of 'String' for these fields
data DataDesc
  = DataDesc {
    dataName :: String
  , dataUpcast :: String
  , dataCtors :: Map Ctor CtorDesc
  }

-- Note: Only constructor arguments that are polymorphic need to have a cast
-- applied.
--
-- In other words, when scrutinizing 'cons @int z zs : list int', 'z' is stored
-- as a 'struct alloc_header *' and 'zs' is stored as a 'struct list *'. The
-- continuation expects 'struct int64_value *' and 'struct list *'.
--
-- Therefore, we must cast 'CAST_INT64(ctor->head)' but can leave 'ctor->tail' as
-- is when suspending.
--
-- More generally, if a data type's constructor has a field of sort 'AllocH
-- aa', then that field should be cast to 't', where the case kind specifies
-- that '[aa := t]'
data CtorDesc
  = CtorDesc {
  -- Hmm. Need a ctorName field to name the struct.
    ctorDiscriminant :: Int
  , ctorAllocate :: String
  , ctorDowncast :: String
  -- Hmm. I think I can compute thunkType from argCasts?
  -- Actually, no not quite. Both can be computed from a constructor's type telescope, though.
  , ctorThunkType :: ThunkType
  , ctorArgCasts :: [(String, Maybe Sort)]
  }

dataDesc :: DataDecl -> [Sort] -> DataDesc
dataDesc (DataDecl tc typarams ctors) tyargs =
  DataDesc {
    dataName = show tc
  , dataUpcast = "CAST_" ++ show tc
  , dataCtors = Map.fromList $ zipWith ctorDesc [0..] ctors
  }
  where
    sub = listSubst (zip (map fst typarams) tyargs)
    -- 'i' is the index of the ctor, and therefore the discriminant for this ctor.
    ctorDesc i (CtorDecl c args) =
      ( c
      , CtorDesc {
        ctorDiscriminant = i
      -- Hmm. If all ctors are distinct, I don't need to namespace with the tycon here.
      -- (e.g., 'cons' only belongs to 'list', so I could call 'make_cons'
      -- instead of 'make_list_cons')
      , ctorAllocate = "allocate_" ++ show tc ++ "_" ++ show c
      , ctorDowncast = "CAST_" ++ show tc ++ "_" ++ show c
      , ctorThunkType = ThunkType thunkTy
      , ctorArgCasts = argCasts
      })
      where
        (thunkTy, argCasts) = unzip (map f args)
        f (fld, AllocH aa) = case lookupSubst aa sub of
          -- All parameters of the data type should have corresponding arguments.
          -- All argument sorts should be well-formed w.r.t. those parameters, so
          -- the 'Nothing' case should not occur.
          --
          -- However, if I add existential ADTs, there may be an argument sort
          -- 'AllocH bb', where 'bb' is existentially bound. In that case, the
          -- argument should be cast to 'struct alloc_header *', I think.
          Nothing -> error "missing type argument"
          Just s' -> (ThunkValueArg s', (show fld, Just s'))
        f (fld, s) = (ThunkValueArg s, (show fld, Nothing))

boolDataDecl :: DataDecl
boolDataDecl =
  -- 'bool' is reserved in C, so I cannot use 'bool' as a type constructor here.
  -- Hrrm. Annoying.
  DataDecl (TyCon "vbool") []
  [ CtorDecl (Ctor "false") []
  , CtorDecl (Ctor "true") []
  ]

sumDataDecl :: DataDecl
sumDataDecl =
  let aa = TyVar (Id "a") in
  let bb = TyVar (Id "b") in
  DataDecl (TyCon "sum") [(aa, Star), (bb, Star)]
  [ CtorDecl (Ctor "inl") [(Id "payload", AllocH aa)]
  , CtorDecl (Ctor "inr") [(Id "payload", AllocH bb)]
  ]

listDataDecl :: DataDecl
listDataDecl =
  let aa = TyVar (Id "a") in
  DataDecl (TyCon "list") [(aa, Star)]
  [ CtorDecl (Ctor "nil") []
  , CtorDecl (Ctor "cons") [(Id "head", AllocH aa), (Id "tail", ListH (AllocH aa))]
  ]

dataDescTable :: TyConApp -> DataDesc
dataDescTable CaseBool = dataDesc boolDataDecl []
dataDescTable (CaseSum t s) = dataDesc sumDataDecl [t, s]
dataDescTable (CaseList t) = dataDesc listDataDecl [t]

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
emitPrimOp envp (PrimConcatenate x y) = emitPrimCall envp "prim_concatenate" [x, y]
emitPrimOp envp (PrimStrlen x) = emitPrimCall envp "prim_strlen" [x]

emitPrimCall :: EnvPtr -> String -> [Name] -> String
emitPrimCall envp fn xs = emitBuiltinCall envp (Id fn) xs

-- Hmm. I can't quite use this for emitValueAlloc, because I cannot specify
-- primitives like unboxed integers or c string literals.
--
-- I also can't use this for emitValueAlloc because if the sort of a parameter
-- is 'AllocH', I need to cast the argument with AS_ALLOC.
emitBuiltinCall :: EnvPtr -> Id -> [Name] -> String
emitBuiltinCall envp fn args = show fn ++ "(" ++ commaSep (map (emitName envp) args) ++ ")"

-- | Allocate a group of (mutually recursive) closures.
--
-- This is a three-step process.
-- - First, each closure's environment is allocated. Cyclic references are
--   initialized with @NULL@.
-- - Second, the closures are allocated using the environments from step 1.
-- - Third, the @NULL@s in the environments are patched to refer to the
--   freshly-allocated closures.
emitClosureGroup :: EnvPtr -> [ClosureAlloc] -> [Line]
emitClosureGroup envp closures =
  map (allocEnv recNames envp) closures ++
  map allocClosure closures ++
  concatMap (patchEnv recNames) closures
  where recNames = Set.fromList [placeName p | ClosureAlloc p _ _ _ <- closures]

extendThunkEnv :: ThunkEnv -> [ClosureAlloc] -> ThunkEnv
extendThunkEnv (ThunkEnv env) allocs =
  ThunkEnv (foldr (uncurry Map.insert) env tys)
  where
    tys = map f allocs
    f (ClosureAlloc p _ _ _) = case placeSort p of
      ClosureH tele -> (LocalName (placeName p), teleThunkType tele)
      _ -> error "closure alloc stored in non-closure place"

allocEnv :: Set Id -> EnvPtr -> ClosureAlloc -> Line
allocEnv recNames envp (ClosureAlloc _p d envPlace (EnvAlloc fields)) =
  "    struct " ++ envTypeName ns' ++ " *" ++ show envPlace ++ " = " ++ call ++ ";"
  where
    ns' = closureEnvName (namesForClosure d)

    call = envAllocName ns' ++ "(" ++ commaSep args ++ ")"
    args = map emitAllocArg fields
    emitAllocArg (EnvValueArg f x) = if Set.member f recNames then "NULL" else emitName envp x

allocClosure :: ClosureAlloc -> Line
allocClosure (ClosureAlloc p d envPlace _env) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep [envArg, enterArg] ++ ");"
  where
    ns = namesForClosure d
    envArg = asAlloc (show envPlace)
    enterArg = closureEnterName ns

patchEnv :: Set Id -> ClosureAlloc -> [Line]
patchEnv recNames (ClosureAlloc _ _ envPlace (EnvAlloc fields)) = concatMap patchField fields
  where
    patchField (EnvValueArg f (LocalName x)) =
      if Set.member f recNames then
        ["    " ++ show envPlace ++ "->" ++ show f ++ " = " ++ show x ++ ";"]
      else
        []
    -- Patching recursive closures should only ever involve local names.
    -- Additionally, we do not have access to an environment pointer in this function.
    patchField (EnvValueArg _ (EnvName _)) = []

emitPlace :: Place -> String
emitPlace (Place s x) = typeForSort s ++ show x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = show x
emitName envp (EnvName x) = show envp ++ "->" ++ show x

