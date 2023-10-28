
module Backend.Emit
    ( emitProgram
    ) where

import Data.List (intersperse)
import Data.Maybe (mapMaybe)

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Graph (SCC(..), stronglyConnComp)

import Backend.IR
import Util

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

type Line = String


-- TODO: ClosureNames is actually the names associated with a code decl, not a
-- closure decl.
data ClosureNames
  = ClosureNames {
    closureCodeName :: String
  , closureEnterName :: String
  , closureGlobalName :: String
  }

namesForCode :: GlobalLabel -> ClosureNames
namesForCode l =
  ClosureNames {
    closureCodeName = show l ++ "_code"
  , closureEnterName = "enter_" ++ show l
  , closureGlobalName = show l
  }

data EnvNames
  = EnvNames {
    envTypeName :: String
  , envInfoName :: String
  , envAllocName :: String
  , envTraceName :: String
  , envCastName :: String
  }

namesForEnv :: TyCon -> EnvNames
namesForEnv (TyCon tc) =
  EnvNames {
    envTypeName = tc
  , envInfoName = tc ++ "_info"
  , envAllocName = "allocate_" ++ tc
  , envTraceName = "trace_" ++ tc
  , envCastName = "CAST_" ++ tc
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


typeFor :: Type -> String
typeFor (AllocH _) = "struct alloc_header *"
typeFor (ClosureH _) = "struct closure *"
typeFor IntegerH = "struct int64_value *"
typeFor StringH = "struct string_value *"
typeFor CharH = "struct char_value *"
typeFor (ProductH _ _) = "struct pair *"
typeFor (TyRecordH _) = "struct record *"
typeFor UnitH = "struct unit *"
typeFor BooleanH = "struct bool_value *"
typeFor TokenH = "struct token *"
typeFor (TyConH tc) = "struct " ++ show tc ++ " *"
typeFor (TyAppH t _) = typeFor t

asType :: Type -> String -> String
asType (AllocH _) x = asAlloc x
asType IntegerH x = "CAST_INT64(" ++ x ++ ")"
asType (ClosureH _) x = "CAST_CLOSURE(" ++ x ++ ")"
asType StringH x = "CAST_STRING(" ++ x ++ ")"
asType CharH x = "CAST_CHAR(" ++ x ++ ")"
asType BooleanH x = "CAST_BOOL(" ++ x ++ ")"
asType (ProductH _ _) x = "CAST_PAIR(" ++ x ++ ")"
asType (TyRecordH _) x = "CAST_RECORD(" ++ x ++ ")"
asType UnitH x = "CAST_UNIT(" ++ x ++ ")"
asType TokenH x = "CAST_TOKEN(" ++ x ++ ")"
asType (TyAppH t _) x = asType t x
asType (TyConH tc) x = "CAST_" ++ show tc ++ "(" ++ x ++ ")"

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
    declThunkTypes acc (DeclEnv _) = acc
    declThunkTypes acc (DeclCode cd) = codeDeclThunkTypes acc cd
    declThunkTypes acc (DeclConst cd) = constDeclThunkTypes acc cd

    codeDeclThunkTypes acc cd@(CodeDecl _ _ _ _ e) =
      -- Note: It is important to record the code decl's thunk type here.
      -- This is because the entry code for this code decl references the
      -- 'args_$ty' struct, which is generated by a thunk type.
      termThunkTypes e <> Set.insert (codeDeclType cd) acc

    constDeclThunkTypes acc (ConstClosure l l') = acc -- I don't think this introduces anything new.

    termThunkTypes (HaltH _ _) = Set.empty
    -- Closure invocations and case analysis suspend a closure, so the
    -- necessary thunk type must be recorded.
    termThunkTypes (OpenH ty _ _) = Set.singleton ty
    termThunkTypes (CaseH _ _ alts) = Set.fromList [ty | CaseAlt _ ty _ <- alts]
    termThunkTypes (IntCaseH _ alts) = Set.fromList [ty | IntCaseAlt _ ty _ <- alts]
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
-- (typeFor requires extra parameter, though... that will require plumbing)


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

emitProgram :: Program -> String
emitProgram pgm@(Program ds e) = unlines $
  prologue ++
  concatMap emitThunkDecl ts ++
  concatMap emitTypeDecls (orderTypeDecls typeDecls) ++
  concatMap (emitGlobalDecls denv) (orderGlobalDecls globalDecls) ++
  emitEntryPoint denv e
  where
    ts = Set.toList (programThunkTypes pgm)
    denv = collectDataEnv ds Map.empty
    (typeDecls, globalDecls) = partitionDecls ds

collectDataEnv :: [Decl] -> DataEnv -> DataEnv
collectDataEnv [] acc = acc
collectDataEnv (DeclCode _cd : ds) acc = collectDataEnv ds acc
collectDataEnv (DeclConst _cd : ds) acc = collectDataEnv ds acc
collectDataEnv (DeclEnv _ed : ds) acc = collectDataEnv ds acc
collectDataEnv (DeclData dd@(DataDecl tc _) : ds) acc = collectDataEnv ds (Map.insert tc dd acc)

partitionDecls :: [Decl] -> ([TypeDecl], [GlobalDecl])
partitionDecls ds = partitionWith f ds
  where
    f (DeclCode cd) = Right (GlobalCode cd)
    f (DeclConst cd) = Right (GlobalConst cd)
    f (DeclData dd) = Left (DataTypeDecl dd)
    f (DeclEnv ed) = Left (EnvTypeDecl ed)

-- hmm. maybe have large combined graph keyed by Either TyCon GlobalLabel?

data TypeDecl = DataTypeDecl DataDecl | EnvTypeDecl EnvDecl -- | RecordTypeDecl RecordDecl

data GlobalDecl = GlobalCode CodeDecl | GlobalConst ConstDecl

typeDeclTyCon :: TypeDecl -> TyCon
typeDeclTyCon (DataTypeDecl (DataDecl tc _)) = tc
typeDeclTyCon (EnvTypeDecl (EnvDecl tc _)) = tc

orderTypeDecls :: [TypeDecl] -> [SCC TypeDecl]
orderTypeDecls ds = stronglyConnComp graph
  where
    graph = [node d | d <- ds]
    node d@(DataTypeDecl (DataDecl tc ctors)) = (d, tc, Set.toList (foldMap deps ctors))
    node d@(EnvTypeDecl (EnvDecl tc fields)) = (d, tc, Set.toList (foldMap fieldDeps fields))
    deps (CtorDecl _c _aas fs) = foldMap fieldDeps fs
    fieldDeps (_, t) = tycons t

orderGlobalDecls :: [GlobalDecl] -> [SCC GlobalDecl]
orderGlobalDecls ds = stronglyConnComp graph
  where
    graph = [node d | d <- ds]
    node d@(GlobalCode cd) = (d, codeDeclName cd, Set.toList (deps cd))
    node d@(GlobalConst (ConstClosure l l')) = (d, l, [l'])
    deps (CodeDecl _l _aas _env _params e) = globalRefs e


emitTypeDecls :: SCC TypeDecl -> [Line]
emitTypeDecls (AcyclicSCC td) = emitTypeDecl td
-- emit forward declaration of each tycon, then the actual struct
-- declarations+prototypes+type info.
emitTypeDecls (CyclicSCC tds) = forwards ++ concatMap emitTypeDecl tds
  where
    forwards = ["struct " ++ show (typeDeclTyCon td) ++ ";" | td <- tds]

emitTypeDecl :: TypeDecl -> [Line]
emitTypeDecl (DataTypeDecl dd) = emitDataDecl dd
emitTypeDecl (EnvTypeDecl ed) = emitClosureEnv ed

emitGlobalDecls :: DataEnv -> SCC GlobalDecl -> [Line]
emitGlobalDecls denv (AcyclicSCC gd) = emitGlobalDecl denv gd
emitGlobalDecls denv (CyclicSCC gds) = forwards ++ concatMap (emitGlobalDecl denv) gds
  where
    forwards = ["void enter_" ++ show (codeDeclName cd) ++ "(void);" | GlobalCode cd <- gds]

emitGlobalDecl :: DataEnv -> GlobalDecl -> [Line]
emitGlobalDecl denv (GlobalCode cd) = emitCodeDecl denv cd
emitGlobalDecl _denv (GlobalConst cd) = emitConstDecl cd


tycons :: Type -> Set TyCon
tycons (TyConH tc) = Set.singleton tc
tycons (AllocH _) = Set.empty
tycons IntegerH = Set.empty
tycons BooleanH = Set.empty
tycons StringH = Set.empty
tycons UnitH = Set.empty
tycons CharH = Set.empty
tycons TokenH = Set.empty
tycons (TyAppH t1 t2) = tycons t1 <> tycons t2
tycons (ProductH t1 t2) = tycons t1 <> tycons t2
tycons (TyRecordH fs) = foldMap (tycons . snd) fs
tycons (ClosureH (ClosureTele tele)) = go tele
  where
    go [] = Set.empty
    go (ValueTele t : tele') = tycons t <> go tele'
    go (TypeTele _ _ : tele') = go tele'

globalRefs :: TermH -> Set GlobalLabel
globalRefs (HaltH _ _) = Set.empty
globalRefs (OpenH _ _ _) = Set.empty
globalRefs (CaseH _ _ _) = Set.empty
globalRefs (IntCaseH _ _) = Set.empty
globalRefs (LetValH _ _ e) = globalRefs e
globalRefs (LetPrimH _ prim e) = globalRefs e
globalRefs (LetBindH _ _ prim e) = globalRefs e
globalRefs (LetProjectH _ _ _ e) = globalRefs e
globalRefs (AllocClosures es cs e) =
  foldMap envGlobalRefs es <> foldMap closureGlobalRefs cs <> globalRefs e
  where
    envGlobalRefs (EnvAlloc _x _tc _fs) = Set.empty -- I think. No code labels here.
    closureGlobalRefs (ClosureAlloc _p l _ts _env) = Set.singleton l





prologue :: [Line]
prologue = ["#include \"rts.h\""]

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

foldThunk :: (Int -> Type -> b) -> ThunkType -> [b]
foldThunk consValue ty = go 0 (thunkArgs ty)
  where
    -- Not quite mapWithIndex because we discard/ignore info arguments.
    go _ [] = []
    go i (ThunkValueArg s : ss) = consValue i s : go (i+1) ss
    go i (ThunkTypeArg : ss) = go i ss

emitThunkArgs :: ThunkNames -> ThunkType -> [Line]
emitThunkArgs ns ty =
  ["struct " ++ thunkArgsName ns ++ " {"
  ,"    struct alloc_header *env;"] ++
  declareFields ty ++
  ["};"]
  where
    declareFields = foldThunk consValue
      where
        consValue i s =
          "    " ++ declareVar s ("arg" ++ show i) ++ ";"

declareVar :: Type -> String -> String
declareVar s x = typeFor s ++ x;

emitThunkTrace :: ThunkNames -> ThunkType -> [Line]
emitThunkTrace ns ty =
  ["void " ++ thunkTraceName ns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    mark_gray(args->env);"] ++
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
  ,"    args->env = closure->env;"] ++
  assignFields ty ++
  ["    set_next(closure->code.enter, " ++ thunkTraceName ns ++ ");"
  ,"}"]
  where
    argsTy = "struct " ++ thunkArgsName ns ++ " *"
    paramList = "struct closure *closure" : foldThunk consValue ty
      where
        consValue i s = declareVar s ("arg" ++ show i)
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
  ,"};"
  ,"#define CAST_" ++ show tc ++ "(v) ((struct " ++ show tc ++ " *)(v))"]

emitCtorDecl :: CtorDecl -> [Line]
emitCtorDecl cd =
  emitCtorStruct cd ++
  emitCtorInfo cd ++
  emitCtorAllocate cd

-- The stem of a C identifier for things related to a particular data
-- constructor, qualified by its type constructor.
-- Eh. could probably use a better name.
ctorQualName :: Ctor -> String
ctorQualName c = show (ctorTyCon c) ++ "_" ++ ctorName c

emitCtorStruct :: CtorDecl -> [Line]
emitCtorStruct (CtorDecl c _tys args) =
  let ctorStructName = ctorQualName c in
  ["struct " ++ ctorStructName ++ " {"
  ,"    struct " ++ show (ctorTyCon c) ++ " header;"] ++
  map makeField args ++
  ["};"
  ,"#define CAST_" ++ ctorStructName ++ "(v) ((struct " ++ ctorStructName ++ " *)(v))"]
  where makeField (f, s) = "    " ++ emitField f s ++ ";"

emitCtorInfo :: CtorDecl -> [Line]
emitCtorInfo (CtorDecl c _tys args) =
  -- Hmm. May need DataNames and CtorNames
  let ctorId = ctorQualName c in
  let ctorCast = "CAST_" ++ ctorId ++ "(alloc)" in
  let name = ctorName c in
  ["void trace_" ++ ctorId ++ "(struct alloc_header *alloc) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ ";"] ++
  map traceField args ++
  ["}"
  ,"void display_" ++ ctorId ++ "(struct alloc_header *alloc, struct string_buf *sb) {"
  ,"    struct " ++ ctorId ++ " *ctor = " ++ ctorCast ++ ";"
  ,"    string_buf_push_slice(sb, " ++ show name ++ ", " ++ show (length name) ++ ");"
  ,"    string_buf_push_slice(sb, \"(\", 1);"] ++
  intersperse "string_buf_push_slice(sb, \", \", 2);" (map displayField args) ++
  ["    string_buf_push_slice(sb, \")\", 1);"
  ,"}"
  ,"const type_info " ++ ctorId ++ "_info = { trace_" ++ ctorId ++ ", display_" ++ ctorId ++ ", " ++ show (ctorDiscriminant c) ++ " };"]
  where
    traceField (x, _s) = "    mark_gray(AS_ALLOC(ctor->" ++ show x ++ "));"
    displayField (x, _s) = "    AS_ALLOC(ctor->" ++ show x ++ ")->info->display(AS_ALLOC(ctor->" ++ show x ++ "), sb);"

emitCtorAllocate :: CtorDecl -> [Line]
emitCtorAllocate (CtorDecl c _tys args) =
  let ctorStructName = ctorQualName c in
  let tc = ctorTyCon c in
  ["struct " ++ show tc ++ " *allocate_" ++ ctorStructName ++ "(" ++ commaSep params ++ ") {"
  ,"    struct " ++ ctorStructName ++ " *ctor = malloc(sizeof(struct " ++ ctorStructName ++ "));"] ++
  map assignField args ++
  ["    cons_new_alloc(AS_ALLOC(ctor), &" ++ ctorStructName ++ "_info);"
  ,"    return CAST_" ++ show tc ++ "(ctor);"
  ,"}"]
  where
    params = [emitField f s | (f, s) <- args]
    assignField (x, _s) = "    ctor->" ++ show x ++ " = " ++ show x ++ ";"


-- This is basically code generation for a named record type.
-- If/when I add user-facing named record types, I could probably generalize
-- this function to implement it.
emitClosureEnv :: EnvDecl -> [Line]
emitClosureEnv (EnvDecl tc fields) =
  let ns = namesForEnv tc in
  emitEnvDecl ns fields ++
  emitEnvInfo ns fields ++
  emitEnvAlloc ns fields

emitEnvDecl :: EnvNames -> [(FieldLabel, Type)] -> [Line]
emitEnvDecl ns fs =
  ["struct " ++ envTypeName ns ++ " {"
  ,"    struct alloc_header header;"] ++
  map mkField fs ++
  ["};"
  ,"#define " ++ envCastName ns ++ "(v) ((struct " ++ envTypeName ns ++ " *)(v))"]
  where
    mkField (f, s) = "    " ++ emitField f s ++ ";"

emitEnvAlloc :: EnvNames -> [(FieldLabel, Type)] -> [Line]
emitEnvAlloc ns fs =
  ["struct " ++ envTypeName ns ++ " *" ++ envAllocName ns ++ "(" ++ paramList ++ ") {"
  ,"    struct " ++ envTypeName ns ++ " *_env = malloc(sizeof(struct " ++ envTypeName ns ++ "));"]++
  map assignField fs ++
  ["    cons_new_alloc(AS_ALLOC(_env), &" ++ envInfoName ns ++ ");"
  ,"    return _env;"
  ,"}"]
  where
    paramList = if null params then "void" else commaSep params
    params = map (\ (f, s) -> emitField f s) fs
    assignField (x, _) = "    _env->" ++ show x ++ " = " ++ show x ++ ";"

emitEnvInfo :: EnvNames -> [(FieldLabel, Type)] -> [Line]
emitEnvInfo ns fs =
  ["void " ++ envTraceName ns ++ "(struct alloc_header *alloc) {"
  ,"    " ++ envTy ++ envName ++ " = " ++ envCastName ns ++ "(alloc);"] ++
  map traceField fs ++
  ["}"
  ,"const type_info " ++ envInfoName ns ++ " = { " ++ envTraceName ns ++ ", display_env, 0 };"]
  where
    envName = "env"
    envTy = "struct " ++ envTypeName ns ++ " *"
    traceField (x, _) =
      let field = asAlloc (envName ++ "->" ++ show x) in
      "    mark_gray(" ++ field ++ ");"


emitCodeDecl :: DataEnv -> CodeDecl -> [Line]
emitCodeDecl denv cd@(CodeDecl l _aas (envName, envTyCon) params e) =
  emitClosureCode denv envTyCon cns envName params e ++
  emitClosureEnter tns envTyCon cns ty
  where
    cns = namesForCode l
    tns = namesForThunk ty
    ty = codeDeclType cd

-- Hmm. emitEntryPoint and emitClosureCode are nearly identical, save for the
-- environment pointer.
emitClosureCode :: DataEnv -> TyCon -> ClosureNames -> Id -> [ClosureParam] -> TermH -> [Line]
emitClosureCode denv envTyCon cns envName xs e =
  ["void " ++ closureCodeName cns ++ "(" ++ paramList ++ ") {"] ++
  emitTerm denv e ++
  ["}"]
  where
    paramList = commaSep (emitPlace envParam : mapMaybe emitParam xs)
    envParam = Place (TyConH envTyCon) envName
    emitParam (TypeParam _ _) = Nothing
    emitParam (PlaceParam p) = Just (emitPlace p)

emitClosureEnter :: ThunkNames -> TyCon -> ClosureNames -> ThunkType -> [Line]
emitClosureEnter tns envTyCon cns ty =
  ["void " ++ closureEnterName cns ++ "(void) {"
  ,"    " ++ argsTy ++ "args = (" ++ argsTy ++ ")argument_data;"
  ,"    " ++ emitPlace (Place envTy envId) ++ " = " ++ asType envTy "args->env" ++ ";"
  ,"    " ++ closureCodeName cns ++ "(" ++ commaSep argList ++ ");"
  ,"}"
  ,"struct code " ++ closureGlobalName cns ++ " = { " ++ closureEnterName cns ++ " };"]
  where
    argsTy = "struct " ++ thunkArgsName tns ++ " *"
    envTy = TyConH envTyCon
    -- This unique is cheating. But this is confined to a local scope, so it's alright.
    envId = Id "env" (Unique 0)
    argList = emitName (LocalName envId) : foldThunk consValue ty
      where consValue i _ = "args->arg" ++ show i


emitConstDecl :: ConstDecl -> [Line]
emitConstDecl (ConstClosure l l') =
  -- hmm. How can I avoid needing a separate declaration for the closure and
  -- the closure reference?
  ["struct closure __static_" ++ show l' ++ " = { { 0, NULL, closure_info }, the_empty_env, " ++ closureGlobalName (namesForCode l') ++ " };"
  ,"struct closure *" ++ show l ++ " = &__static_" ++ show l' ++ ";"]


emitTerm :: DataEnv -> TermH -> [Line]
emitTerm denv (LetValH x v e) =
  ["    " ++ emitPlace x ++ " = " ++ emitValue denv v ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetProjectH x y ProjectFst e) =
  ["    " ++ emitPlace x ++ " = " ++ asType (placeType x) (emitName y ++ "->fst") ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetProjectH x y ProjectSnd e) =
  ["    " ++ emitPlace x ++ " = " ++ asType (placeType x) (emitName y ++ "->snd") ++ ";"] ++
  emitTerm denv e
emitTerm denv (LetProjectH x y (ProjectField (FieldLabel f)) e) =
  ["    " ++ emitPlace x ++ " = " ++ asType (placeType x) ("project_field(" ++ emitName y ++ ", " ++ show f ++ ", " ++ show (length f) ++ ")") ++ ";"] ++
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
  ["    switch (" ++ emitName x ++ "->header.info->discriminant) {"] ++
  concatMap emitCaseBranch branches ++
  ["    default:"
  ,"        unreachable(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch :: CaseAlt -> [String]
    emitCaseBranch (CaseAlt c ty k) =
      let
        argCasts = ctorArgCasts (dataCtors desc Map.! c)
        ctorVal = "CAST_" ++ ctorQualName c ++ "(" ++ emitName x ++ ")"
        method = thunkSuspendName (namesForThunk ty)
        args = emitName k : map mkArg argCasts
        mkArg (argName, Nothing) = ctorVal ++ "->" ++ argName
        mkArg (argName, Just argType) = asType argType (ctorVal ++ "->" ++ argName)
      in
        ["    case " ++ show (ctorDiscriminant c) ++ ":"
        ,"        " ++ method ++ "(" ++ commaSep args ++ ");"
        ,"        break;"]

emitIntCase :: Name -> [IntCaseAlt] -> [Line]
emitIntCase x branches =
  ["    switch(" ++ emitName x ++ "->value) {"] ++
  concatMap emitCaseBranch branches ++
  ["    default:"
  ,"        unreachable(\"invalid discriminant\");"
  ,"    }"]
  where
    emitCaseBranch (IntCaseAlt i ty k) =
      let
        method = thunkSuspendName (namesForThunk ty)
      in
        ["    case " ++ show i ++ ":"
        ,"        " ++ method ++ "(" ++ emitName k ++ ");"
        ,"        break;"]

emitValue :: DataEnv -> ValueH -> String
emitValue _ (IntH i) = "allocate_int64(" ++ show i ++ ")"
emitValue _ (BoolH b) = if b then "allocate_bool_value(1)" else "allocate_bool_value(0)"
emitValue _ (StringValH s) = "allocate_string(" ++ show s ++ ", " ++ show (length s) ++ ")"
emitValue _ (CharValH c) = "allocate_char(" ++ show c ++ ")"
emitValue _ (PairH x y) = emitBuiltinCall "allocate_pair" [UpCastArg x, UpCastArg y]
emitValue _ NilH = "allocate_unit()"
emitValue _ WorldToken = "allocate_token()"
emitValue _ (RecordH fields) =
  "allocate_record(" ++ show (length fields) ++
  ", (struct field_init[]){" ++ commaSep (map initField fields) ++ "})"
  where
    initField (FieldLabel f, x) = "{" ++ commaSep [show f, show (length f), asAlloc (emitName x)] ++ "}"
emitValue denv (CtorAppH c ss xs) =
  -- We need to know the type of ctor 'c', so that we know which arguments need
  -- to be cast with 'asAlloc'. This is the 'ctorArgCasts' in 'DataDesc'.
  -- Thus, we construct 'tcapp' from 'c's type constructor and the fact that
  -- 'ss' is the list of universal type arguments to this constructor.
  let tcapp = TyConApp (ctorTyCon c) ss in
  let desc = dataDescFor denv tcapp in
  emitCtorAlloc desc (c, xs)


emitCtorAlloc :: DataDesc -> (Ctor, [Name]) -> String
emitCtorAlloc desc (ctor, xs) = method ++ "(" ++ commaSep args' ++ ")"
  where
    method = "allocate_" ++ show (ctorTyCon ctor) ++ "_" ++ ctorName ctor

    argCasts = ctorArgCasts (dataCtors desc Map.! ctor)
    args' = map emitCtorArg (zipWith makeArg xs argCasts)
    makeArg x (_, Nothing) = NormalArg x
    makeArg x (_, Just _) = UpCastArg x

emitCtorArg :: CtorArg -> String
emitCtorArg (NormalArg x) = emitName x
emitCtorArg (UpCastArg x) = asAlloc (emitName x)
emitCtorArg (DownCastArg s x) = asType s (emitName x)

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
  = CtorDesc { ctorArgCasts :: [(String, Maybe Type)] }

dataDesc :: DataDecl -> [Type] -> DataDesc
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
emitPrimCall fn xs = emitBuiltinCall fn (map NormalArg xs)

-- Hmm. I can't quite use this for emitValueAlloc, because I cannot specify
-- primitives like unboxed integers or c string literals.
--
-- I also can't use this for emitValueAlloc because if the sort of a parameter
-- is 'AllocH', I need to cast the argument with AS_ALLOC.
emitBuiltinCall :: String -> [CtorArg] -> String
emitBuiltinCall fn args = fn ++ "(" ++ commaSep (map emitCtorArg args) ++ ")"


-- TODO: Use SCC-based analysis to codegen allocations of recursive value groups
-- (This would let me generalize ClosureAlloc/EnvAlloc to just being ordinary
-- groups of value bindings -- assuming I make environments just named record
-- types as I plan to)

-- emitValueGroup :: [(Place, ValueH)] -> [Line]
-- emitValueGroup binds = _
--
-- orderValueGroup :: [(Place, ValueH)] -> [SCC (Place, ValueH)] -- key on Id
-- orderValueGroup binds = _
--
-- assignValueGroup :: SCC (Place, ValueH) -> [Line]
-- assignValueGroup (AcyclicSCC (p, v)) = _ -- normal assignment
-- -- have to pick loop breakers somehow, I think.
-- -- Alternatively, DFS, and emit a NULL/patch for each back edge encountered(?)
-- assignValueGroup (CyclicSCC ps) = _

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
  where
    -- If constructing an environment references a name in the bind group
    -- (which is necessarily a LocalName), we must initialize it with NULL and
    -- patch it afterwards.
    recNames = Set.fromList [LocalName (placeName p) | ClosureAlloc p _ _ _ <- closures]

allocEnv :: Set Name -> EnvAlloc -> Line
allocEnv _ (EnvAlloc envPlace _ []) =
  "    " ++ emitPlace (Place (TyConH (TyCon "empty_env")) envPlace) ++ " = the_empty_env;"
allocEnv recNames (EnvAlloc envPlace tc fields) =
  "    " ++ emitPlace (Place (TyConH tc) envPlace) ++ " = " ++ call ++ ";"
  where
    -- Hrrm. I would like to replace 'tc' with a general 'Type, so that
    -- environment allocations are very similar to value allocations (and so
    -- that I could theoretically have an environment value that *isn't* a
    -- named record type -- e.g. if there's only one field, store that field
    -- directly).
    -- 
    -- However, I can't quite do that, because I don't have a way to allocate a
    -- generic value (because anonymous records have complex initializers that
    -- don't really fit into an expression spot)
    call = "allocate_" ++ show tc ++ "(" ++ commaSep args ++ ")"
    args = map emitAllocArg fields
    emitAllocArg (_f, x) = if Set.member x recNames then "NULL" else emitName x

allocClosure :: ClosureAlloc -> Line
allocClosure (ClosureAlloc p l _tys envRef) =
  "    " ++ emitPlace p ++ " = allocate_closure(" ++ commaSep [envArg, enterArg] ++ ");"
  where
    envArg = asAlloc (emitName (LocalName envRef))
    enterArg = closureGlobalName (namesForCode l)

patchEnv :: Set Name -> EnvAlloc -> [Line]
patchEnv recNames (EnvAlloc envPlace _ fields) = mapMaybe patchField fields
  where
    patchField (f, x) =
      if Set.member x recNames then
        let envf = EnvName envPlace f in
        Just ("    " ++ emitName envf ++ " = " ++ emitName x ++ ";")
      else
        Nothing

-- Hmm. Consider breaking up into semantically distinct operations:
-- (Would still be effectively identical code, though.
-- (Could help future refactors by disentangling concepts, perhaps?)
-- * declareParam place = <type> <ident>
-- * declareField = <type> <ident> ;
-- * declareLocal place = <type> <ident> ;
-- * assignLocal place initializer = <type> <ident> = <init.exp>; <init.body>
emitPlace :: Place -> String
emitPlace (Place s x) = typeFor s ++ show x

emitName :: Name -> String
emitName (LocalName x) = show x
emitName (EnvName envp x) = show envp ++ "->" ++ show x

emitField :: FieldLabel -> Type -> String
emitField f s = typeFor s ++ show f

