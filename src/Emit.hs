
module Emit
    ( emitProgram
    ) where

import Data.List (intercalate, intersperse)
import Data.Maybe (mapMaybe)
import Data.Traversable (mapAccumL)

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- import Hoist.IR
import Lower2

-- TODO: Something smarter than string and list concatenation.
-- builders? text? environment?
-- Reader EmitEnv T.Builder -- no monoid instance
-- EmitEnv -> T.Builder -- monoid instance

-- At a minimum, Austral's C backend is slightly refined: return list of line,
-- where line is (indentation level :: Int, line contents :: String)
-- (See https://borretti.me/article/design-austral-compiler#crender for
-- details)

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
typeForSort (ProductH _ _) = "struct pair *"
typeForSort UnitH = "struct unit *"
typeForSort BooleanH = "struct vbool *"
typeForSort TokenH = "struct token *"
typeForSort (SumH _ _) = "struct sum *"
typeForSort (TyConH tc) = "struct " ++ show tc ++ " *"
typeForSort (TyAppH t _) = typeForSort t

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort IntegerH x = "CAST_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "CAST_CLOSURE(" ++ x ++ ")"
asSort StringH x = "CAST_STRING(" ++ x ++ ")"
asSort BooleanH x = "CAST_bool(" ++ x ++ ")"
asSort (ProductH _ _) x = "CAST_PAIR(" ++ x ++ ")"
asSort (SumH _ _) x = "CAST_sum(" ++ x ++ ")"
asSort UnitH x = "CAST_UNIT(" ++ x ++ ")"
asSort TokenH x = "CAST_TOKEN(" ++ x ++ ")"
asSort (TyAppH t _) x = asSort t x
asSort (TyConH tc) x = "CAST_" ++ show tc ++ "(" ++ x ++ ")"

asAlloc :: String -> String
asAlloc x = "AS_ALLOC(" ++ x ++ ")"


-- | Compute the thunk type of a closure declaration.
codeDeclType :: CodeDecl -> ThunkType
codeDeclType decl = teleThunkType (codeDeclTele decl)

-- | Compute the set of thunk types (calling conventions) used by a program, so
-- that appropriate support code can be generated.
programThunkTypes :: Program -> Set ThunkType
programThunkTypes (Program decls mainExpr) = declThunks <> termThunkTypes mainExpr
  where
    declThunks = foldl declThunkTypes Set.empty decls
    declThunkTypes acc (DeclData _) = acc
    declThunkTypes acc (DeclCode cd) = codeDeclThunkTypes acc cd

    codeDeclThunkTypes acc cd@(CodeDecl _ _ _ _ e) =
      -- Note: It is important to record the code decl's thunk type here.
      -- This is because the entry code for this code decl references the
      -- 'args_$ty' struct, which is generated by a thunk type.
      termThunkTypes e <> Set.insert (codeDeclType cd) acc

    termThunkTypes (HaltH _ _) = Set.empty
    -- Closure invocations and case analysis suspend a closure, so the
    -- necessary thunk type must be recorded.
    termThunkTypes (OpenH ty _ _) = Set.singleton ty
    termThunkTypes (CaseH _ _ alts) = Set.fromList [ty | CaseAlt _ ty _ <- alts]
    termThunkTypes (LetValH _ _ e) = termThunkTypes e
    termThunkTypes (LetPrimH _ _ e) = termThunkTypes e
    termThunkTypes (LetBindH _ _ prim e) = termThunkTypes e -- can a primop record a thunk type?
    termThunkTypes (LetProjectH _ _ _ e) = termThunkTypes e
    termThunkTypes (AllocClosure _ e) = termThunkTypes e

-- programRecordTypes :: Program -> Set RecordType
-- Hmm. Existential types can be thought of as records with type fields.
-- Out of scope for MVP, but could be interesting for the future.

-- Hmm. Could use RecordTrie () to collect record types.
-- RecordTrie has empty, singleton, union
-- Once collected, use traverse to assign ids/type names
-- While doing codegen, lookup record type in trie to determine name of type.
-- (typeForSort requires extra parameter, though... that will require plumbing)


-- Hmm. Two ideas:
-- One: support named record types in Hoist as MVP. Anonymous (closed) records
-- can later be implemented by giving them a name. (Even simple named records
-- are still useful as a front-end feature: e.g. Parser.run)
-- I should permit duplicate field names, by having 'e.l' work if the type of
-- 'e' is a record type with a field 'l'.
-- I don't really care about record updates, but I should still think about them.
--
-- Two: There is increasing amounts of complexity after Hoist but before proper codegen.
-- I propose a new IR layer, tentatively called "Lower", whose purpose is to
-- ensure that every type has a name, that calling conventions are explicit,
-- etc. etc.
-- (this would take care of gathering thunk types/closure types; monomorphising
-- record types, annotating closure calls with the correct calling convention,
-- etc.)


type DataEnv = Map TyCon DataDecl

emitProgram :: Program -> [Line]
emitProgram pgm@(Program ds e) =
  prologue ++
  concatMap emitThunkDecl ts ++
  concat decls ++
  emitEntryPoint denv e
  where
    ts = Set.toList (programThunkTypes pgm)
    (denv, decls) = mapAccumL emitDecl Map.empty ds

prologue :: [Line]
prologue = ["#include \"rts.h\""]

emitDecl :: DataEnv -> Decl -> (DataEnv, [Line])
emitDecl denv (DeclCode cd) =
  (denv, emitClosureDecl denv cd)
emitDecl denv (DeclData dd@(DataDecl tc _ _)) =
  let denv' = Map.insert tc dd denv in
  (denv', emitDataDecl dd)

emitEntryPoint :: DataEnv -> TermH -> [Line]
emitEntryPoint denv e =
  ["void program_entry(void) {"] ++
  emitTerm denv envp e ++
  ["}"]
  -- There is no environment pointer at the top level, because we are not in a closure.
  where envp = Id "NULL"


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
    -- Not quite mapWithIndex because we discard/ignore info arguments.
    go _ [] = []
    go i (ThunkValueArg s : ss) = consValue i s : go (i+1) ss
    go i (ThunkTypeArg : ss) = go i ss

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


emitDataDecl :: DataDecl -> [Line]
emitDataDecl (DataDecl tc params ctors) =
  emitDataStruct tc ++
  concatMap emitCtorDecl ctors

emitDataStruct :: TyCon -> [Line]
emitDataStruct tc =
  ["struct " ++ show tc ++ " {"
  ,"    struct alloc_header header;"
  ,"    uint32_t discriminant;"
  ,"};"
  ,"#define CAST_" ++ show tc ++ "(v) ((struct " ++ show tc ++ " *)(v))"]

emitCtorDecl :: CtorDecl -> [Line]
emitCtorDecl cd =
  emitCtorStruct cd ++
  emitCtorInfo cd ++
  emitCtorAllocate cd

emitCtorStruct :: CtorDecl -> [Line]
emitCtorStruct (CtorDecl tc c _i args) =
  let ctorId = show tc ++ "_" ++ show c in
  ["struct " ++ ctorId ++ " {"
  ,"    struct " ++ show tc ++ " header;"] ++
  map makeField args ++
  ["};"
  ,"#define CAST_" ++ ctorId ++ "(v) ((struct " ++ ctorId ++ " *)(v))"]
  where makeField (x, s) = "    " ++ emitPlace (Place s x) ++ ";"

emitCtorInfo :: CtorDecl -> [Line]
emitCtorInfo (CtorDecl tc c _i args) =
  -- Hmm. May need DataNames and CtorNames
  let ctorId = show tc ++ "_" ++ show c in
  let ctorCast = "CAST_" ++ ctorId in
  ["void trace_" ++ ctorId ++ "(struct alloc_header *alloc) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ "(alloc);"] ++
  map traceField args ++
  ["}"
  ,"void display_" ++ ctorId ++ "(struct alloc_header *alloc, struct string_buf *sb) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ "(alloc);"
  ,"    string_buf_push_slice(sb, " ++ ctorNameString ++ ", " ++ show ctorNameLen ++ ");"
  ,"    string_buf_push_slice(sb, \"(\", 1);"] ++
  intersperse "string_buf_push_slice(sb, \", \", 2);" (map displayField args) ++
  ["    string_buf_push_slice(sb, \")\", 1);"
  ,"}"
  ,"const type_info " ++ ctorId ++ "_info = { trace_" ++ ctorId ++ ", display_" ++ ctorId ++ " };"]
  where
    ctorNameString = show (show c)
    ctorNameLen = length (show c)
    traceField (x, s) = "    mark_gray(AS_ALLOC(ctor->" ++ show x ++ "));"
    displayField (x, s) = "    AS_ALLOC(ctor->" ++ show x ++ ")->info->display(AS_ALLOC(ctor->" ++ show x ++ "), sb);"

emitCtorAllocate :: CtorDecl -> [Line]
emitCtorAllocate (CtorDecl tc c i args) =
  let ctorId = show tc ++ "_" ++ show c in
  ["struct " ++ show tc ++ " *allocate_" ++ ctorId ++ "(" ++ commaSep params ++ ") {"
  ,"    struct " ++ ctorId ++ " *ctor = malloc(sizeof(struct " ++ ctorId ++ "));"
  ,"    ctor->header.discriminant = " ++ show i ++ ";"] ++
  map assignField args ++
  ["    cons_new_alloc(AS_ALLOC(ctor), &" ++ ctorId ++ "_info);"
  ,"    return CAST_" ++ show tc ++ "(ctor);"
  ,"}"]
  where
    params = [emitPlace (Place s x) | (x, s) <- args]
    assignField (x, s) = "    ctor->" ++ show x ++ " = " ++ show x ++ ";"


emitClosureDecl :: DataEnv -> CodeDecl -> [Line]
emitClosureDecl denv cd@(CodeDecl d _aas (envName, places) params e) =
  emitClosureEnv cns places ++
  emitClosureCode denv cns envName params e ++
  emitClosureEnter tns cns ty
  where
    cns = namesForClosure d
    tns = namesForThunk ty
    ty = codeDeclType cd

-- It would be nice if each closure didn't have to generate its own record type.
-- This is part of what I hope to achieve with Lower.IR
-- (Instead, Lower.IR.CodeDecl would contain a TyCon/TyConApp for the type of
-- its environment.)
emitClosureEnv :: ClosureNames -> [Place] -> [Line]
emitClosureEnv ns envd =
  let ns' = closureEnvName ns in
  emitEnvDecl ns' envd ++
  emitEnvInfo ns' envd ++
  emitEnvAlloc ns' envd

-- These need better names, to reflect the fact that an environment is
-- basically just a record type.
emitEnvDecl :: EnvNames -> [Place] -> [Line]
emitEnvDecl ns fs =
  ["struct " ++ envTypeName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkField fs ++
  ["};"]
  where
    mkField f = "    " ++ emitPlace f ++ ";"

emitEnvAlloc :: EnvNames -> [Place] -> [Line]
emitEnvAlloc ns fs =
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

emitEnvInfo :: EnvNames -> [Place] -> [Line]
emitEnvInfo ns fs =
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
emitClosureCode :: DataEnv -> ClosureNames -> Id -> [ClosureParam] -> TermH -> [Line]
emitClosureCode denv ns envName xs e =
  ["void " ++ closureCodeName ns ++ "(" ++ paramList ++ ") {"] ++
  emitTerm denv envName e ++
  ["}"]
  where
    paramList = commaSep (envParam : mapMaybe emitParam xs)
    envParam = "struct " ++ envTypeName (closureEnvName ns) ++ " *" ++ show envName
    emitParam (TypeParam _ _) = Nothing
    emitParam (PlaceParam p) = Just (emitPlace p)


emitTerm :: DataEnv -> EnvPtr -> TermH -> [Line]
emitTerm denv envp (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValueAlloc denv envp (placeSort x) v ++ ";"] ++
  emitTerm denv envp e
emitTerm denv envp (LetProjectH x y ProjectFst e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->fst") ++ ";"] ++
  emitTerm denv envp e
emitTerm denv envp (LetProjectH x y ProjectSnd e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName envp y ++ "->snd") ++ ";"] ++
  emitTerm denv envp e
emitTerm denv envp (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp envp p ++ ";"] ++
  emitTerm denv envp e
emitTerm denv envp (LetBindH p1 p2 prim e) =
  ["    " ++ emitPlace p1 ++ ";"
  ,"    " ++ emitPlace p2 ++ ";"
  ,"    " ++ emitPrimIO envp prim p1 p2 ++ ";"] ++
  emitTerm denv envp e
emitTerm denv envp (AllocClosure cs e) =
  emitClosureGroup envp cs ++
  emitTerm denv envp e
emitTerm _ envp (HaltH _ x) =
  ["    halt_with(" ++ asAlloc (emitName envp x) ++ ");"]
emitTerm _ envp (OpenH ty c args) =
  [emitSuspend ty envp c args]
emitTerm denv envp (CaseH x kind ks) =
  emitCase denv kind envp x ks

emitSuspend :: ThunkType -> EnvPtr -> Name -> [ClosureArg] -> Line
emitSuspend ty envp cl xs =
  "    " ++ method ++ "(" ++ commaSep args ++ ");"
  where
    method = thunkSuspendName (namesForThunk ty)
    args = emitName envp cl : mapMaybe makeArg (zip (thunkArgs ty) xs)

    makeArg (ThunkTypeArg, TypeArg i) = Nothing
    makeArg (ThunkValueArg _, ValueArg y) = Just (emitName envp y)
    makeArg _ = error "calling convention mismatch: type/value param paired with value/type arg"


-- Hrmm. I would like to move DataEnv into Lower2 to simplify Emit, but DataEnv
-- has many ideas that are specific to the C backend, such as argument casts
-- and struct downcasts.
--
-- Maybe I should consider Hoist to be the last "platform-independent" pass,
-- and have Lower2 be considered part of the C backend?
--
-- Maybe a compromise? suspend method and discriminant are fairly universal, so
-- they can go into Lower2. Struct downcasts and argument casts are C-specific,
-- so they can stay here.
emitCase :: DataEnv -> TyConApp -> EnvPtr -> Name -> [CaseAlt] -> [Line]
emitCase denv tcapp envp x branches =
  ["    switch (" ++ emitName envp x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch branches ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    desc = dataDescFor denv tcapp

    emitCaseBranch :: CaseAlt -> [String]
    emitCaseBranch (CaseAlt ctor ty k) =
      let
        ctordesc = dataCtors desc Map.! ctor
        ctorVal = ctorDowncast ctordesc ++ "(" ++ emitName envp x ++ ")"
        method = thunkSuspendName (namesForThunk ty)
        args = emitName envp k : map mkArg (ctorArgCasts ctordesc)
        mkArg (argName, Nothing) = ctorVal ++ "->" ++ argName
        mkArg (argName, Just argSort) = asSort argSort (ctorVal ++ "->" ++ argName)
      in
        ["    case " ++ show (ctorDiscriminant ctordesc) ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

emitValueAlloc :: DataEnv -> EnvPtr -> Sort -> ValueH -> String
emitValueAlloc _ _ _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValueAlloc _ _ _ (StringValH s) =
  "allocate_string(" ++ show s ++ ", " ++ show (length s) ++ ")"
emitValueAlloc _ envp _ (PairH x y) =
  "allocate_pair(" ++ asAlloc (emitName envp x) ++ ", " ++ asAlloc (emitName envp y) ++ ")"
emitValueAlloc _ _ _ NilH = "allocate_unit()"
emitValueAlloc _ _ _ WorldToken = "allocate_token()"
emitValueAlloc denv envp ty (CtorAppH capp) =
  case asTyConApp ty of
    Nothing -> error "not a constructed type"
    Just kind -> emitCtorAlloc denv envp kind capp

emitCtorAlloc :: DataEnv -> EnvPtr -> TyConApp -> CtorAppH -> String
emitCtorAlloc denv envp kind capp = ctorAllocate ctordesc ++ "(" ++ commaSep args' ++ ")"
  where
    desc = dataDescFor denv kind
    ctordesc = dataCtors desc Map.! ctorName
    (ctorName, args) = case capp of
      BoolH True -> (Ctor "true", [])
      BoolH False -> (Ctor "false", [])
      InlH x -> (Ctor "inl", [x])
      InrH x -> (Ctor "inr", [x])
      CtorApp c as -> (c, as)
    args' = zipWith makeArg args (ctorArgCasts ctordesc)
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
    ctorDiscriminant :: Int -- Instead of raw int, consider an enum for ctor tags?
  , ctorAllocate :: String
  , ctorDowncast :: String
  , ctorSuspend :: String
  , ctorArgCasts :: [(String, Maybe Sort)]
  }

dataDesc :: DataDecl -> [Sort] -> DataDesc
dataDesc (DataDecl tycon typarams ctors) tyargs =
  DataDesc {
    dataName = show tycon
  , dataUpcast = "CAST_" ++ show tycon
  , dataCtors = Map.fromList $ map ctorDesc ctors
  }
  where
    sub = listSubst (zip (map fst typarams) tyargs)
    ctorDesc (CtorDecl tc c i args) =
      ( c
      , CtorDesc {
        ctorDiscriminant = i
      -- Hmm. If all ctors are distinct, I don't need to namespace with the tycon here.
      -- (e.g., 'cons' only belongs to 'list', so I could call 'make_cons'
      -- instead of 'make_list_cons')
      , ctorAllocate = "allocate_" ++ show tc ++ "_" ++ show c
      , ctorDowncast = "CAST_" ++ show tc ++ "_" ++ show c
      , ctorSuspend = thunkSuspendName (namesForThunk (ThunkType thunkTy))
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
          Nothing -> error "missing argument in tyconapp"
          Just s' -> (ThunkValueArg s', (show fld, Just s'))
        f (fld, s) = (ThunkValueArg s, (show fld, Nothing))

boolDataDecl :: DataDecl
boolDataDecl =
  -- 'bool' is reserved in C, so I cannot use 'bool' as a type constructor here.
  -- Hrrm. Annoying.
  let tc = TyCon "vbool" in
  DataDecl tc []
  [ CtorDecl tc (Ctor "false") 0 []
  , CtorDecl tc (Ctor "true") 1 []
  ]

sumDataDecl :: DataDecl
sumDataDecl =
  let tc = TyCon "sum" in
  let aa = TyVar (Id "a") in
  let bb = TyVar (Id "b") in
  DataDecl tc [(aa, Star), (bb, Star)]
  [ CtorDecl tc (Ctor "inl") 0 [(Id "payload", AllocH aa)]
  , CtorDecl tc (Ctor "inr") 1 [(Id "payload", AllocH bb)]
  ]

dataDescFor :: DataEnv -> TyConApp -> DataDesc
dataDescFor _ CaseBool = dataDesc boolDataDecl []
dataDescFor _ (CaseSum t s) = dataDesc sumDataDecl [t, s]
dataDescFor denv (TyConApp tc args) = dataDesc (denv Map.! tc) args

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

emitPrimIO :: EnvPtr -> PrimIO -> Place -> Place -> String
emitPrimIO envp (PrimGetLine x) p1 p2 =
  "prim_getLine(" ++ commaSep [emitName envp x, '&' : show (placeName p1), '&' : show (placeName p2)] ++ ")"
emitPrimIO envp (PrimPutLine x y) p1 p2 = 
  "prim_putLine(" ++ commaSep [emitName envp x, emitName envp y, '&' : show (placeName p1), '&' : show (placeName p2)] ++ ")"

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
  where recNames = Set.fromList [placeName p | ClosureAlloc p _ _ _ _ <- closures]

allocEnv :: Set Id -> EnvPtr -> ClosureAlloc -> Line
allocEnv recNames envp (ClosureAlloc _p d _inst envPlace fields) =
  "    struct " ++ envTypeName ns' ++ " *" ++ show envPlace ++ " = " ++ call ++ ";"
  where
    ns' = closureEnvName (namesForClosure d)

    call = envAllocName ns' ++ "(" ++ commaSep args ++ ")"
    args = map emitAllocArg fields
    emitAllocArg (f, x) = if Set.member f recNames then "NULL" else emitName envp x

allocClosure :: ClosureAlloc -> Line
allocClosure (ClosureAlloc p d _tys envPlace _env) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep [envArg, enterArg] ++ ");"
  where
    ns = namesForClosure d
    envArg = asAlloc (show envPlace)
    enterArg = closureEnterName ns

patchEnv :: Set Id -> ClosureAlloc -> [Line]
patchEnv recNames (ClosureAlloc _ _ _ envPlace fields) = concatMap patchField fields
  where
    patchField (f, LocalName x) =
      if Set.member f recNames then
        ["    " ++ show envPlace ++ "->" ++ show f ++ " = " ++ show x ++ ";"]
      else
        []
    -- Patching recursive closures should only ever involve local names.
    -- Additionally, we do not have access to an environment pointer in this function.
    patchField (_, EnvName _) = []

emitPlace :: Place -> String
emitPlace (Place s x) = typeForSort s ++ show x

emitName :: EnvPtr -> Name -> String
emitName _ (LocalName x) = show x
emitName envp (EnvName x) = show envp ++ "->" ++ show x

