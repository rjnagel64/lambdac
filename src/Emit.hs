
module Emit
    ( emitProgram
    ) where

import Data.Int (Int64)
import Data.List (intercalate, intersperse)
import Data.Maybe (mapMaybe)
import Data.Traversable (mapAccumL)

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Lower

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

type Line = String


data ClosureNames
  = ClosureNames {
    closureCodeName :: String
  , closureEnterName :: String
  }

namesForClosure :: CodeLabel -> ClosureNames
namesForClosure (CodeLabel f) =
  ClosureNames {
    closureCodeName = f ++ "_code"
  , closureEnterName = "enter_" ++ f
  }

data EnvNames
  = EnvNames {
    envTypeName :: String
  , envInfoName :: String
  , envAllocName :: String
  , envTraceName :: String
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
  let code = thunkTypeCode ty in
  ThunkNames {
    thunkTypeName = "thunk_" ++ code
  , thunkArgsName = "args_" ++ code
  , thunkTraceName = "trace_args_" ++ code
  , thunkSuspendName = "suspend_" ++ code
  }


typeForSort :: Sort -> String
typeForSort (AllocH _) = "struct alloc_header *"
typeForSort (ClosureH _) = "struct closure *"
typeForSort IntegerH = "struct int64_value *"
typeForSort StringH = "struct string_value *"
typeForSort CharH = "struct char_value *"
typeForSort (ProductH _ _) = "struct pair *"
typeForSort (TyRecordH _) = "struct record *"
typeForSort UnitH = "struct unit *"
typeForSort BooleanH = "struct bool_value *"
typeForSort TokenH = "struct token *"
typeForSort (TyConH tc) = "struct " ++ show tc ++ " *"
typeForSort (TyAppH t _) = typeForSort t

asSort :: Sort -> String -> String
asSort (AllocH _) x = asAlloc x
asSort IntegerH x = "CAST_INT64(" ++ x ++ ")"
asSort (ClosureH _) x = "CAST_CLOSURE(" ++ x ++ ")"
asSort StringH x = "CAST_STRING(" ++ x ++ ")"
asSort CharH x = "CAST_CHAR(" ++ x ++ ")"
asSort BooleanH x = "CAST_BOOL(" ++ x ++ ")"
asSort (ProductH _ _) x = "CAST_PAIR(" ++ x ++ ")"
asSort (TyRecordH _) x = "CAST_RECORD(" ++ x ++ ")"
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
    termThunkTypes (IntCaseH _ alts) = Set.fromList [ty | (_, ty, _) <- alts]
    termThunkTypes (LetValH _ _ e) = termThunkTypes e
    termThunkTypes (LetPrimH _ _ e) = termThunkTypes e
    termThunkTypes (LetBindH _ _ prim e) = termThunkTypes e -- can a primop record a thunk type?
    termThunkTypes (LetProjectH _ _ _ e) = termThunkTypes e
    termThunkTypes (AllocClosures _ _ e) = termThunkTypes e

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
emitDecl denv (DeclData dd@(DataDecl tc _)) =
  let denv' = Map.insert tc dd denv in
  (denv', emitDataDecl dd)

emitEntryPoint :: DataEnv -> TermH -> [Line]
emitEntryPoint denv e =
  ["void program_entry(void) {"] ++
  emitTerm denv e ++
  ["}"]


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
emitDataDecl (DataDecl tc ctors) =
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
emitCtorStruct (CtorDecl (Ctor tc c _i) _tys args) =
  let ctorId = show tc ++ "_" ++ show c in
  ["struct " ++ ctorId ++ " {"
  ,"    struct " ++ show tc ++ " header;"] ++
  map makeField args ++
  ["};"
  ,"#define CAST_" ++ ctorId ++ "(v) ((struct " ++ ctorId ++ " *)(v))"]
  where makeField (x, s) = "    " ++ emitPlace (Place s x) ++ ";"

emitCtorInfo :: CtorDecl -> [Line]
emitCtorInfo (CtorDecl (Ctor tc c _i) _tys args) =
  -- Hmm. May need DataNames and CtorNames
  let ctorId = show tc ++ "_" ++ show c in
  let ctorCast = "CAST_" ++ ctorId in
  ["void trace_" ++ ctorId ++ "(struct alloc_header *alloc) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ "(alloc);"] ++
  map traceField args ++
  ["}"
  ,"void display_" ++ ctorId ++ "(struct alloc_header *alloc, struct string_buf *sb) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ "(alloc);"
  ,"    string_buf_push_slice(sb, " ++ show cname ++ ", " ++ show (length cname) ++ ");"
  ,"    string_buf_push_slice(sb, \"(\", 1);"] ++
  intersperse "string_buf_push_slice(sb, \", \", 2);" (map displayField args) ++
  ["    string_buf_push_slice(sb, \")\", 1);"
  ,"}"
  ,"const type_info " ++ ctorId ++ "_info = { trace_" ++ ctorId ++ ", display_" ++ ctorId ++ " };"]
  where
    cname = show c
    traceField (x, _s) = "    mark_gray(AS_ALLOC(ctor->" ++ show x ++ "));"
    displayField (x, _s) = "    AS_ALLOC(ctor->" ++ show x ++ ")->info->display(AS_ALLOC(ctor->" ++ show x ++ "), sb);"

emitCtorAllocate :: CtorDecl -> [Line]
emitCtorAllocate (CtorDecl (Ctor tc c i) _tys args) =
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
    assignField (x, _s) = "    ctor->" ++ show x ++ " = " ++ show x ++ ";"


emitClosureDecl :: DataEnv -> CodeDecl -> [Line]
emitClosureDecl denv cd@(CodeDecl d _aas (envName, fields) params e) =
  emitClosureEnv envd ++
  emitClosureCode denv ens cns envName params e ++
  emitClosureEnter tns ens cns ty
  where
    envd = EnvDecl d fields
    cns = namesForClosure d
    ens = namesForEnv d
    tns = namesForThunk ty
    ty = codeDeclType cd

-- This should be migrated up into Lower.IR
-- (And it should have a TyCon instead of a CodeLabel)
data EnvDecl
  = EnvDecl CodeLabel [(Id, Sort)]

-- It would be nice if each closure didn't have to generate its own record type.
-- This is part of what I hope to achieve with Lower.IR
-- (Instead, Lower.IR.CodeDecl would contain a TyCon/TyConApp for the type of
-- its environment.)
emitClosureEnv :: EnvDecl -> [Line]
emitClosureEnv (EnvDecl d fields) =
  let ns = namesForEnv d in
  emitEnvDecl ns fields ++
  emitEnvInfo ns fields ++
  emitEnvAlloc ns fields

-- These need better names, to reflect the fact that an environment is
-- basically just a record type.
emitEnvDecl :: EnvNames -> [(Id, Sort)] -> [Line]
emitEnvDecl ns fs =
  ["struct " ++ envTypeName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkField fs ++
  ["};"]
  where
    mkField (x, s) = "    " ++ emitPlace (Place s x) ++ ";"

emitEnvAlloc :: EnvNames -> [(Id, Sort)] -> [Line]
emitEnvAlloc ns fs =
  ["struct " ++ envTypeName ns ++ " *" ++ envAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ envTypeName ns ++ " *_env = malloc(sizeof(struct " ++ envTypeName ns ++ "));"]++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(_env), &" ++ envInfoName ns ++ ");"
  ,"    return _env;"
  ,"}"]
  where
    paramList = if null params then "void" else commaSep params
    params = map (\ (x, s) -> emitPlace (Place s x)) fs
    assignField (x, _) = "    _env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: EnvNames -> [(Id, Sort)] -> [Line]
emitEnvInfo ns fs =
  ["void " ++ envTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ show envName ++ " = (" ++ envTy ++ ")alloc;"] ++
  map traceField fs ++
  ["}"
  ,"const type_info " ++ envInfoName ns ++ " = { " ++ envTraceName ns ++ ", display_env };"]
  where
    envName = Id "env"
    envTy = "struct " ++ envTypeName ns ++ " *"
    traceField (x, _) =
      let field = asAlloc (emitName (EnvName envName x)) in
      "    mark_gray(" ++ field ++ ");"

emitClosureEnter :: ThunkNames -> EnvNames -> ClosureNames -> ThunkType -> [Line]
emitClosureEnter tns ens cns ty =
  ["void " ++ closureEnterName cns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    " ++ envTy ++ "env = (" ++ envTy ++ ")args->closure->env;"
  ,"    " ++ closureCodeName cns ++ "(" ++ commaSep argList ++ ");"
  ,"}"]
  where
    argsTy = "struct " ++ thunkArgsName tns ++ " *"
    envTy = "struct " ++ envTypeName ens ++ " *"
    argList = "env" : foldThunk consValue ty
      where consValue i _ = "args->arg" ++ show i

-- Hmm. emitEntryPoint and emitClosureCode are nearly identical, save for the
-- environment pointer.
emitClosureCode :: DataEnv -> EnvNames -> ClosureNames -> Id -> [ClosureParam] -> TermH -> [Line]
emitClosureCode denv ens cns envName xs e =
  ["void " ++ closureCodeName cns ++ "(" ++ paramList ++ ") {"] ++
  emitTerm denv e ++
  ["}"]
  where
    paramList = commaSep (envParam : mapMaybe emitParam xs)
    envParam = "struct " ++ envTypeName ens ++ " *" ++ show envName
    emitParam (TypeParam _ _) = Nothing
    emitParam (PlaceParam p) = Just (emitPlace p)


emitTerm :: DataEnv -> TermH -> [Line]
emitTerm denv (LetValH x v e) =
  emitValueDefinition denv x v ++
  emitTerm denv e
emitTerm denv (LetProjectH x y ProjectFst e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName y ++ "->fst") ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetProjectH x y ProjectSnd e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) (emitName y ++ "->snd") ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetProjectH x y (ProjectField (FieldLabel f)) e) =
  ["    " ++ emitPlace x ++ " = " ++ asSort (placeSort x) ("project_field(" ++ emitName y ++ ", " ++ show f ++ ", " ++ show (length f) ++ ")") ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetPrimH x p e) =
  ["    " ++ emitPlace x ++ " = " ++ emitPrimOp p ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetBindH p1 p2 prim e) =
  ["    " ++ emitPlace p1 ++ ";"
  ,"    " ++ emitPlace p2 ++ ";"
  ,"    " ++ emitPrimIO prim p1 p2 ++ ";"] ++
  emitTerm denv e
emitTerm denv (AllocClosures es cs e) =
  emitClosureGroup es cs ++
  emitTerm denv e
emitTerm _ (HaltH _ x) =
  ["    halt_with(" ++ asAlloc (emitName x) ++ ");"]
emitTerm _ (OpenH ty c args) =
  [emitSuspend ty c args]
emitTerm denv (CaseH x tcapp ks) =
  let desc = dataDescFor denv tcapp in
  emitCase desc x ks
emitTerm _ (IntCaseH x ks) =
  emitIntCase x ks

emitSuspend :: ThunkType -> Name -> [ClosureArg] -> Line
emitSuspend ty cl xs =
  "    " ++ method ++ "(" ++ commaSep args ++ ");"
  where
    method = thunkSuspendName (namesForThunk ty)
    args = emitName cl : mapMaybe makeArg (zip (thunkArgs ty) xs)

    makeArg (ThunkTypeArg, TypeArg _) = Nothing
    makeArg (ThunkValueArg _, ValueArg x) = Just (emitName x)
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
emitCase :: DataDesc -> Name -> [CaseAlt] -> [Line]
emitCase desc x branches =
  ["    switch (" ++ emitName x ++ "->discriminant) {"] ++
  concatMap emitCaseBranch branches ++
  ["    default:"
  ,"        panic(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: CaseAlt -> [String]
    emitCaseBranch (CaseAlt c@(Ctor tc ctor i) ty k) =
      let
        argCasts = ctorArgCasts (dataCtors desc Map.! c)
        ctorVal = "CAST_" ++ show tc ++ "_" ++ show ctor ++ "(" ++ emitName x ++ ")"
        method = thunkSuspendName (namesForThunk ty)
        args = emitName k : map mkArg argCasts
        mkArg (argName, Nothing) = ctorVal ++ "->" ++ argName
        mkArg (argName, Just argSort) = asSort argSort (ctorVal ++ "->" ++ argName)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

emitIntCase :: Name -> [(Int64, ThunkType, Name)] -> [Line]
emitIntCase x branches =
  ["    switch(" ++ emitName x ++ "->value) {"] ++
  concatMap emitCaseBranch branches ++
  ["    default:"
  ,"        panic(\"invalid value for case analysis\");"
  ,"    }"]
  where
    emitCaseBranch (i, ty, k) =
      let
        method = thunkSuspendName (namesForThunk ty)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ emitName k ++ ");"
        ,"        break;"]

emitValueDefinition :: DataEnv -> Place -> ValueH -> [Line]
emitValueDefinition _ p (IntH i) =
  defineLocal p ("allocate_int64(" ++ show i ++ ")") []
emitValueDefinition _ p (BoolH b) =
  defineLocal p (if b then "allocate_bool_value(1)" else "allocate_bool_value(0)") []
emitValueDefinition _ p (StringValH s) =
  defineLocal p ("allocate_string(" ++ show s ++ ", " ++ show (length s) ++ ")") []
emitValueDefinition _ p (CharValH c) =
  defineLocal p ("allocate_char(" ++ show c ++ ")") []
emitValueDefinition _ p (PairH x y) =
  defineLocal p ("allocate_pair(" ++ asAlloc (emitName x) ++ ", " ++ asAlloc (emitName y) ++ ")") []
emitValueDefinition _ p NilH =
  defineLocal p "allocate_unit()" []
emitValueDefinition _ p WorldToken =
  defineLocal p "allocate_token()" []
emitValueDefinition _ p (RecordH fields) =
  defineLocal p ("allocate_record(" ++ show (length fields) ++ ")") fields'
  where
    fields' = concatMap assignField (zip [0..] fields)
    assignField :: (Int, (FieldLabel, Name)) -> [Line]
    assignField (i, (FieldLabel label, x)) =
      let lval = show (placeName p) ++ "->fields[" ++ show i ++ "]" in
      ["    " ++ lval ++ ".label = allocate_string(" ++ show label ++ ", " ++ show (length label) ++ ");"
      ,"    " ++ lval ++ ".value = " ++ asAlloc (emitName x) ++ ";"]
emitValueDefinition denv p (CtorAppH capp) =
  case asTyConApp (placeSort p) of
    Nothing -> error "not a constructed type"
    Just tcapp ->
      let desc = dataDescFor denv tcapp in
      defineLocal p (emitCtorAlloc desc capp) []

emitCtorAlloc :: DataDesc -> CtorAppH -> String
emitCtorAlloc desc (CtorApp ctor xs) = method ++ "(" ++ commaSep args' ++ ")"
  where
    method = "allocate_" ++ show (ctorTyCon ctor) ++ "_" ++ show (ctorName ctor)

    argCasts = ctorArgCasts (dataCtors desc Map.! ctor)
    args' = zipWith makeArg xs argCasts
    makeArg x (_, Nothing) = emitName x
    makeArg x (_, Just _) = asAlloc (emitName x)

data DataDesc
  = DataDesc {
    dataCtors :: Map Ctor CtorDesc
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
  = CtorDesc { ctorArgCasts :: [(String, Maybe Sort)] }

dataDesc :: DataDecl -> [Sort] -> DataDesc
dataDesc (DataDecl _tycon ctors) tyargs =
  DataDesc {
    dataCtors = Map.fromList $ map ctorDesc ctors
  }
  where
    ctorDesc (CtorDecl c tys args) =
      (c, CtorDesc { ctorArgCasts = argCasts })
      where
        sub = listSubst (zip (map fst tys) tyargs)
        argCasts = map f args
        f (fld, AllocH aa) = case lookupSubst aa sub of
          -- All parameters of the data type should have corresponding arguments.
          -- All argument sorts should be well-formed w.r.t. those parameters, so
          -- the 'Nothing' case should not occur.
          --
          -- However, if I add existential ADTs, there may be an argument sort
          -- 'AllocH bb', where 'bb' is existentially bound. In that case, the
          -- argument should be cast to 'struct alloc_header *', I think.
          Nothing -> error "missing argument in tyconapp"
          Just s' -> (show fld, Just s')
        f (fld, _s) = (show fld, Nothing)

dataDescFor :: DataEnv -> TyConApp -> DataDesc
dataDescFor denv (TyConApp tc args) = dataDesc (denv Map.! tc) args

emitPrimOp :: PrimOp -> String
emitPrimOp (PrimAddInt64 x y) = emitPrimCall "prim_addint64" [x, y]
emitPrimOp (PrimSubInt64 x y) = emitPrimCall "prim_subint64" [x, y]
emitPrimOp (PrimMulInt64 x y) = emitPrimCall "prim_mulint64" [x, y]
emitPrimOp (PrimNegInt64 x) = emitPrimCall "prim_negint64" [x]
emitPrimOp (PrimEqInt64 x y) = emitPrimCall "prim_eqint64" [x, y]
emitPrimOp (PrimNeInt64 x y) = emitPrimCall "prim_neint64" [x, y]
emitPrimOp (PrimLtInt64 x y) = emitPrimCall "prim_ltint64" [x, y]
emitPrimOp (PrimLeInt64 x y) = emitPrimCall "prim_leint64" [x, y]
emitPrimOp (PrimGtInt64 x y) = emitPrimCall "prim_gtint64" [x, y]
emitPrimOp (PrimGeInt64 x y) = emitPrimCall "prim_geint64" [x, y]
emitPrimOp (PrimEqChar x y) = emitPrimCall "prim_eqchar" [x, y]
emitPrimOp (PrimConcatenate x y) = emitPrimCall "prim_concatenate" [x, y]
emitPrimOp (PrimStrlen x) = emitPrimCall "prim_strlen" [x]
emitPrimOp (PrimIndexStr x y) = emitPrimCall "prim_strindex" [x, y]

emitPrimIO :: PrimIO -> Place -> Place -> String
emitPrimIO (PrimGetLine x) p1 p2 =
  "prim_getLine(" ++ commaSep [emitName x, '&' : show (placeName p1), '&' : show (placeName p2)] ++ ")"
emitPrimIO (PrimPutLine x y) p1 p2 = 
  "prim_putLine(" ++ commaSep [emitName x, emitName y, '&' : show (placeName p1), '&' : show (placeName p2)] ++ ")"

emitPrimCall :: String -> [Name] -> String
emitPrimCall fn xs = emitBuiltinCall (Id fn) xs

-- Hmm. I can't quite use this for emitValueAlloc, because I cannot specify
-- primitives like unboxed integers or c string literals.
--
-- I also can't use this for emitValueAlloc because if the sort of a parameter
-- is 'AllocH', I need to cast the argument with AS_ALLOC.
emitBuiltinCall :: Id -> [Name] -> String
emitBuiltinCall fn args = show fn ++ "(" ++ commaSep (map emitName args) ++ ")"

-- | Allocate a group of (mutually recursive) closures.
--
-- This is a three-step process.
-- - First, each closure's environment is allocated. Cyclic references are
--   initialized with @NULL@.
-- - Second, the closures are allocated using the environments from step 1.
-- - Third, the @NULL@s in the environments are patched to refer to the
--   freshly-allocated closures.
emitClosureGroup :: [EnvAlloc] -> [ClosureAlloc] -> [Line]
emitClosureGroup envs closures =
  map (allocEnv recNames) envs ++
  map allocClosure closures ++
  concatMap (patchEnv recNames) envs
  where recNames = Set.fromList [placeName p | ClosureAlloc p _ _ _ <- closures]

allocEnv :: Set Id -> EnvAlloc -> Line
allocEnv recNames (EnvAlloc envPlace d fields) =
  "    struct " ++ envTypeName ns ++ " *" ++ show envPlace ++ " = " ++ call ++ ";"
  where
    ns = namesForEnv d

    call = envAllocName ns ++ "(" ++ commaSep args ++ ")"
    args = map emitAllocArg fields
    emitAllocArg (f, x) = if Set.member f recNames then "NULL" else emitName x

allocClosure :: ClosureAlloc -> Line
allocClosure (ClosureAlloc p d _tys envRef) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep [envArg, enterArg] ++ ");"
  where
    ns = namesForClosure d
    envArg = asAlloc (emitName (LocalName envRef))
    enterArg = closureEnterName ns

patchEnv :: Set Id -> EnvAlloc -> [Line]
patchEnv recNames (EnvAlloc envPlace _ fields) = mapMaybe patchField fields
  where
    patchField (f, LocalName x) =
      if Set.member f recNames then
        Just ("    " ++ show envPlace ++ "->" ++ show f ++ " = " ++ show x ++ ";")
      else
        Nothing
    -- Patching recursive closures should only ever involve local names.
    -- (An environment reference cannot possibly be part of this recursive bind
    -- group, so we never need to patch a field whose value is obtained from an
    -- EnvName)
    patchField (_, EnvName _ _) = Nothing

-- Define a local variable, by giving it a name+type, an initializer, and an
-- optional list of field initializers.
--
-- (A higher-level API could/should be used instead of string-typing)
defineLocal :: Place -> String -> [Line] -> [Line]
defineLocal p initVal fields =
  [emitPlace p ++ " = " ++ initVal ++ ";"] ++
  fields

-- Hmm. Consider breaking up into semantically distinct operations:
-- (Would still be effectively identical code, though.
-- (Could help future refactors by disentangling concepts, perhaps?)
-- * declareParam place = <type> <ident>
-- * declareField = <type> <ident> ;
-- * declareLocal place = <type> <ident> ;
-- * assignLocal place initializer = <type> <ident> = <init.exp>; <init.body>
emitPlace :: Place -> String
emitPlace (Place s x) = typeForSort s ++ show x

emitName :: Name -> String
emitName (LocalName x) = show x
emitName (EnvName envp x) = show envp ++ "->" ++ show x

