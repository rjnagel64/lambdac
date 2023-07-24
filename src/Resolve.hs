
module Resolve
  ( resolveProgram

  , Program(..)
  , DataDecl(..)
  , CtorDecl(..)
  , Term(..)
  , Type(..)
  , Kind(..)
  , TmArith(..)
  , TmCmp(..)
  , TmStringOp(..)
  , ID(..)
  , FieldLabel(..)

  , pprintError
  , pprintType
  , pprintKind
  ) where

import Data.List (intercalate)
import Data.Traversable (for)

import qualified Core.IR as S

import Control.Monad.Reader
import Control.Monad.State

import Data.Loc

import qualified Data.Map as Map
import Data.Map (Map)

import Data.Functor.Identity
import Control.Applicative (liftA, liftA2, liftA3) -- wat. why is liftA2 not in Prelude?


-- | Utility function for inserting many items at once.
insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs


resolveProgram :: Program -> Either [ResolveError] S.Program
resolveProgram (Program ds e) = runM $ fmap resolved $ do
  withDataDecls ds $ \ds' -> do
    e' <- resolveTerm e
    pure (S.Program <$> ds' <*> e')
  where
    resolved (Resolved a) = Right a
    resolved (Error es) = Left es

withDataDecls :: [DataDecl] -> (Resolved [S.DataDecl] -> M a) -> M a
withDataDecls [] cont = cont (Resolved [])
withDataDecls (d:ds) cont =
  withDataDecl d $ \rd' ->
    withDataDecls ds $ \rds' ->
      cont ((:) <$> rd' <*> rds')

withDataDecl :: DataDecl -> (Resolved S.DataDecl -> M a) -> M a
withDataDecl (DataDecl tc as ctors) cont = do
  let k = foldr KiArr KiStar (map snd as)
  withTyCon tc k $ \tc' k' -> do
    -- bring group of ctors into scope, in parallel
    withCtors as ctors $ \ctors' -> do
      -- kind of hacky. It would be better for Source and subsequent IRs to be
      -- like GADTs, with the data decl having a kind signature, but the tyvars
      -- being confined to each constructor.
      as' <- traverse (\ (L _ (ID a), k) -> liftA2 (,) <$> pure (Resolved (S.TyVar a)) <*> resolveKind k) as
      cont (S.DataDecl tc' <$> sequenceA as' <*> ctors')

-- bring a set of constructors into scope, in parallel.
withCtors :: [(L ID, Kind)] -> [CtorDecl] -> (Resolved [S.CtorDecl] -> M a) -> M a
withCtors as ctors cont = do
  uniq <- assertDistinctIDs [c | CtorDecl c _ <- ctors]

  (binds, ctors') <- fmap unzip . for ctors $ \ (CtorDecl (L _ c@(ID ident)) args) -> do
    let c' = S.Ctor ident
    withTyVars as $ \as' -> do
      args' <- traverse resolveType args
      -- I should include the as' in the new ctor decl
      pure ((c, c'), S.CtorDecl <$> Resolved c' <*> sequenceA args')

  let extend env = env { ctxCons = insertMany binds (ctxCons env) }
  local extend $ cont (uniq *> sequenceA ctors')

withRecBinds :: [(L ID, Type, Term)] -> (Resolved [(S.TmVar, S.Type, S.Term)] -> M a) -> M a
withRecBinds xs cont = do
  uniq <- assertDistinctIDs [x | (x, _, _) <- xs]

  (binds, ys) <- fmap unzip . for xs $ \ (L _ x@(ID ident), t, e) -> do
    let x' = S.TmVar ident
    t' <- resolveType t
    pure ((x, x'), (x', t', e))

  let extend env = env { ctxVars = insertMany binds (ctxVars env) }
  local extend $ do
    xs' <- for ys $ \ (x', t', e) -> do
      e' <- resolveTerm e
      pure ((,,) x' <$> t' <*> e')
    cont (uniq *> sequenceA xs')

assertDistinctIDs :: [L ID] -> M (Resolved ())
assertDistinctIDs xs =
  case foldr f ([], Map.empty) xs of
    ([], _) -> pure (Resolved ())
    (es, _) -> pure (Error es)
  where
    f (L l x) (es, seen) =
      case Map.lookup x seen of
        Just l' -> (DuplicateBinder l l' x : es, seen)
        Nothing -> (es, Map.insert x l seen)

resolveTerm :: Term -> M (Resolved S.Term)
resolveTerm (TmNameOcc (L l x)) = do
  tmVarEnv <- asks ctxVars
  ctorEnv <- asks ctxCons
  case (Map.lookup x tmVarEnv, Map.lookup x ctorEnv) of
    (Nothing, Nothing) -> pure (Error [NameNotInScope l x])
    (Just x', Nothing) -> pure (Resolved (S.TmVarOcc x'))
    (Nothing, Just x') -> pure (Resolved (S.TmCtorOcc x'))
    (Just _, Just _) -> pure (Error [AmbiguousName l x])
resolveTerm TmNil = pure (Resolved S.TmNil)
resolveTerm TmGetLine = pure (Resolved S.TmGetLine)
resolveTerm (TmInt i) = pure (Resolved (S.TmInt i))
resolveTerm (TmBool b) = pure (Resolved (S.TmBool b))
resolveTerm (TmString s) = pure (Resolved (S.TmString s))
resolveTerm (TmChar c) = pure (Resolved (S.TmChar c))
resolveTerm (TmPure e) = liftA S.TmPure <$> resolveTerm e
resolveTerm (TmPutLine e) = liftA S.TmPutLine <$> resolveTerm e
resolveTerm (TmRunIO e) = liftA S.TmRunIO <$> resolveTerm e
resolveTerm (TmFst e) = liftA S.TmFst <$> resolveTerm e
resolveTerm (TmSnd e) = liftA S.TmSnd <$> resolveTerm e
resolveTerm (TmFieldProj e l) = liftA2 S.TmFieldProj <$> resolveTerm e <*> resolveFieldLabel l
resolveTerm (TmPair e1 e2) = liftA2 S.TmPair <$> resolveTerm e1 <*> resolveTerm e2
resolveTerm (TmRecord fs) = (liftA S.TmRecord . sequenceA) <$> traverse resolveField fs
  where resolveField (l, e) = liftA2 (,) <$> resolveFieldLabel l <*> resolveTerm e
resolveTerm (TmArith e1 op e2) =
  liftA3 S.TmArith <$> resolveTerm e1 <*> resolveArith op <*> resolveTerm e2
resolveTerm (TmNegate e) = liftA S.TmNegate <$> resolveTerm e
resolveTerm (TmCmp e1 op e2) =
  liftA3 S.TmCmp <$> resolveTerm e1 <*> resolveCmp op <*> resolveTerm e2
resolveTerm (TmStringOp e1 op e2) =
  liftA3 S.TmStringOp <$> resolveTerm e1 <*> resolveStringOp op <*> resolveTerm e2
resolveTerm (TmStringLength e) =
  liftA S.TmStringLength <$> resolveTerm e
resolveTerm (TmApp e1 e2) = liftA2 S.TmApp <$> resolveTerm e1 <*> resolveTerm e2
resolveTerm (TmTApp e t) = liftA2 S.TmTApp <$> resolveTerm e <*> resolveType t
resolveTerm (TmLam x t e) = do
  withTmVar x t $ \xt' -> do
    e' <- resolveTerm e
    pure (uncurry S.TmLam <$> xt' <*> e')
resolveTerm (TmTLam a k e) = do
  withTyVar a k $ \ak' -> do
    e' <- resolveTerm e
    pure (uncurry S.TmTLam <$> ak' <*> e')
resolveTerm (TmLet x t e1 e2) = do
  e1' <- resolveTerm e1
  withTmVar x t $ \xt' -> do
    e2' <- resolveTerm e2
    pure (uncurry S.TmLet <$> xt' <*> e1' <*> e2')
resolveTerm (TmTypeAlias x k t e) = do
  withTypeAlias x k t $ do
    e' <- resolveTerm e
    pure e'
resolveTerm (TmBind x t e1 e2) = do
  e1' <- resolveTerm e1
  withTmVar x t $ \xt' -> do
    e2' <- resolveTerm e2
    pure (uncurry S.TmBind <$> xt' <*> e1' <*> e2')
resolveTerm (TmLetRec xs e) = do
  withRecBinds xs $ \xs' -> do
    e' <- resolveTerm e
    pure (S.TmLetRec <$> xs' <*> e')
resolveTerm (TmCase e s alts) = do
  e' <- resolveTerm e
  s' <- resolveType s
  alts' <- for alts $ \ (L l c, xs, rhs) -> do
    envCtors <- asks ctxCons
    c' <- case Map.lookup c envCtors of
      Nothing -> pure (Error [NameNotInScope l c])
      Just c' -> pure (Resolved c')
    withTmVars xs $ \xs' -> do
      rhs' <- resolveTerm rhs
      pure ((,,) <$> c' <*> xs' <*> rhs')
  pure (S.TmCase <$> e' <*> s' <*> sequenceA alts')
resolveTerm (TmIf ec s et ef) = do
  ec' <- resolveTerm ec
  s' <- resolveType s
  et' <- resolveTerm et
  ef' <- resolveTerm ef
  pure (S.TmIf <$> ec' <*> s' <*> et' <*> ef')

resolveType :: Type -> M (Resolved S.Type)
resolveType (TyNameOcc (L l x)) = resolveTyNameOcc (L l x) []
resolveType TyUnit = pure (Resolved S.TyUnit)
resolveType TyInt = pure (Resolved S.TyInt)
resolveType TyBool = pure (Resolved S.TyBool)
resolveType TyString = pure (Resolved S.TyString)
resolveType TyChar = pure (Resolved S.TyChar)
resolveType (TyProd t s) = liftA2 S.TyProd <$> resolveType t <*> resolveType s
resolveType (TyArr t s) = liftA2 S.TyArr <$> resolveType t <*> resolveType s
resolveType (TyIO t) = liftA S.TyIO <$> resolveType t
resolveType (TyRecord fs) = do
  fs' <- traverse resolveField fs
  pure (liftA S.TyRecord (sequenceA fs'))
  where
    resolveField :: (FieldLabel, Type) -> M (Resolved (S.FieldLabel, S.Type))
    resolveField (l, t) = liftA2 (,) <$> resolveFieldLabel l <*> resolveType t
resolveType (TyAll a k t) = do
  withTyVar a k $ \ak' -> do
    t' <- resolveType t
    pure (uncurry S.TyAll <$> ak' <*> t')
resolveType (TyApp t s) = go t [s]
  where
    go :: Type -> [Type] -> M (Resolved S.Type)
    -- Search for the head of this sequence of type applications, collecting
    -- the arguments as we go.
    go (TyApp t' s') args = go t' (s' : args)
    -- The head of the argument is a name reference. Resolve it in the context
    -- of these arguments.
    go (TyNameOcc x) args = resolveTyNameOcc x args
    -- If the head of the application isn't a name, just apply the arguments like normal.
    -- This will probably fail Core.TypeCheck, but name resolution is currently
    -- separate from type-checking, so that isn't our problem. (yet.)
    go ty args = do
      ty' <- resolveType ty
      args' <- traverse resolveType args
      pure (tyAppMany <$> ty' <*> sequenceA args')

resolveTyNameOcc :: L ID -> [Type] -> M (Resolved S.Type)
resolveTyNameOcc (L l x) args = do
  tyVars <- asks ctxTyVars
  tyCons <- asks ctxTyCons
  aliases <- asks ctxAliases
  case (Map.lookup x tyVars, Map.lookup x tyCons, Map.lookup x aliases) of
    (Just x', Nothing, Nothing) -> do
      args' <- traverse resolveType args
      pure (tyAppMany <$> Resolved (S.TyVarOcc x') <*> sequenceA args')
    (Nothing, Just x', Nothing) -> do
      args' <- traverse resolveType args
      pure (tyAppMany <$> Resolved (S.TyConOcc x') <*> sequenceA args')
    (Nothing, Nothing, Just (params, body)) -> do
      let nparams = length params
      let nargs = length args
      if nargs < nparams then
        -- underapplied: error
        pure (Error [UnderAppliedSynonym l x nparams nargs])
      else do
        args' <- traverse resolveType args
        -- fully applied or overapplied: gather 'nparams' args in a TyAliasApp,
        -- and tyAppMany the rest.
        let rFullRest = splitAt nparams <$> sequenceA args'
        let (fullArgs, restArgs) = (fst <$> rFullRest, snd <$> rFullRest)
        let ralias = S.TyAliasApp params <$> fullArgs <*> body
        pure (tyAppMany <$> ralias <*> restArgs)
    (Nothing, Nothing, Nothing) -> pure (Error [NameNotInScope l x])
    (_, _, _) -> pure (Error [AmbiguousName l x])

tyAppMany :: S.Type -> [S.Type] -> S.Type
tyAppMany t ts = foldl (\acc s -> S.TyApp acc s) t ts


resolveKind :: Kind -> M (Resolved S.Kind)
resolveKind KiStar = pure (Resolved S.KiStar)
resolveKind (KiArr k1 k2) = liftA2 S.KiArr <$> resolveKind k1 <*> resolveKind k2

resolveArith :: TmArith -> M (Resolved S.TmArith)
resolveArith TmArithAdd = pure (Resolved S.TmArithAdd)
resolveArith TmArithSub = pure (Resolved S.TmArithSub)
resolveArith TmArithMul = pure (Resolved S.TmArithMul)

resolveCmp :: TmCmp -> M (Resolved S.TmCmp)
resolveCmp TmCmpEq = pure (Resolved S.TmCmpEq)
resolveCmp TmCmpNe = pure (Resolved S.TmCmpNe)
resolveCmp TmCmpLt = pure (Resolved S.TmCmpLt)
resolveCmp TmCmpLe = pure (Resolved S.TmCmpLe)
resolveCmp TmCmpGt = pure (Resolved S.TmCmpGt)
resolveCmp TmCmpGe = pure (Resolved S.TmCmpGe)
resolveCmp TmCmpEqChar = pure (Resolved S.TmCmpEqChar)

resolveStringOp :: TmStringOp -> M (Resolved S.TmStringOp)
resolveStringOp TmConcat = pure (Resolved S.TmConcat)
resolveStringOp TmIndexStr = pure (Resolved S.TmIndexStr)

resolveFieldLabel :: FieldLabel -> M (Resolved S.FieldLabel)
resolveFieldLabel (FieldLabel l) = pure (Resolved (S.FieldLabel l))

withTmVars :: Traversable t => t (L ID, Type) -> (Resolved (t (S.TmVar, S.Type)) -> M a) -> M a
withTmVars xs cont = do
  initEnv <- ask
  (xs', newEnv) <- runStateT (sequenceA <$> traverse resolveBind xs) initEnv
  local (\_ -> newEnv) $ cont xs'
  where
    resolveBind (L _ x@(ID ident), t) = StateT $ \env -> do
      let x' = S.TmVar ident
      t' <- resolveType t
      let bind = (,) x' <$> t'
      pure (bind, env { ctxVars = Map.insert x x' (ctxVars env) })

withTmVar :: L ID -> Type -> (Resolved (S.TmVar, S.Type) -> M a) -> M a
withTmVar x t cont =
  withTmVars (Identity (x, t)) $ \rb -> cont (fmap runIdentity rb)

withTyVars :: Traversable t => t (L ID, Kind) -> (Resolved (t (S.TyVar, S.Kind)) -> M a) -> M a
withTyVars as cont = do
  initEnv <- ask
  (as', newEnv) <- runStateT (sequenceA <$> traverse resolveBind as) initEnv
  local (\_ -> newEnv) $ cont as'
  where
    resolveBind (L _ a@(ID ident), k) = StateT $ \env -> do
      let a' = S.TyVar ident
      k' <- resolveKind k
      let bind = (,) a' <$> k'
      pure (bind, env { ctxTyVars = Map.insert a a' (ctxTyVars env) })

withTyVar :: L ID -> Kind -> (Resolved (S.TyVar, S.Kind) -> M a) -> M a
withTyVar a k cont = withTyVars (Identity (a, k)) $ \rb -> cont (fmap runIdentity rb)

withTyCon :: L ID -> Kind -> (S.TyCon -> Resolved S.Kind -> M a) -> M a
withTyCon (L _ tc@(ID ident)) k cont = do
  let tc' = S.TyCon ident
  k' <- resolveKind k
  let extend env = env { ctxTyCons = Map.insert tc tc' (ctxTyCons env) }
  local extend $ cont tc' k'

withTypeAlias :: L ID -> Kind -> Type -> M a -> M a
withTypeAlias (L _ tc) k t m = do
  t' <- resolveType t
  -- hmm. I don't like the fact that I ignore the kind signature.
  -- Couple that with how Resolve eliminates most of the type alias, does this
  -- mean that type aliases don't get kind-checked?
  --
  -- It might be worthwhile after all to persist type aliases through Core, and
  -- then eliminate them for CPS.
  let extend env = env { ctxAliases = Map.insert tc ([], t') (ctxAliases env) }
  local extend $ m


newtype M a = M { getM :: Reader Context a }

deriving instance Functor M
deriving instance Applicative M
deriving instance Monad M
deriving instance MonadReader Context M

data Context
  = Context {
    ctxVars :: Map ID S.TmVar
  , ctxCons :: Map ID S.Ctor
  , ctxTyVars :: Map ID S.TyVar
  , ctxTyCons :: Map ID S.TyCon
  , ctxAliases :: Map ID ([(S.TyVar, S.Kind)], Resolved S.Type)
  }

runM :: M a -> a
runM = flip runReader emptyContext . getM
  where
    emptyContext = Context {
        ctxVars = Map.empty
      , ctxCons = Map.empty
      , ctxTyVars = Map.empty
      , ctxTyCons = Map.empty
      , ctxAliases = Map.empty
      }

-- | The result of performing name resolution. It is either something
-- successfully resolved to a value of type @a@, or it is a collection of error
-- messages.
data Resolved a
  = Resolved a
  | Error [ResolveError]

data ResolveError
  = NameNotInScope Loc ID
  | AmbiguousName Loc ID
  | DuplicateBinder Loc Loc ID
  | UnderAppliedSynonym Loc ID Int Int

instance Functor Resolved where
  fmap f (Resolved a) = Resolved (f a)
  fmap _ (Error es) = Error es

instance Applicative Resolved where
  pure = Resolved

  Resolved f <*> Resolved x = Resolved (f x)
  Resolved _ <*> Error es = Error es
  Error es <*> Resolved _ = Error es
  Error es1 <*> Error es2 = Error (es1 <> es2)


-- | A generic identifier, that will be resolved to an appropriate type by this pass.
newtype ID = ID String
  deriving (Eq, Ord)

instance Show ID where
  show (ID x) = x

-- | A name used to identify a record field.
-- TODO: Replace Resolve.FieldLabel with ID?
newtype FieldLabel = FieldLabel String
  deriving (Eq)

instance Show FieldLabel where
  show (FieldLabel f) = f


data Program = Program [DataDecl] Term

data DataDecl = DataDecl (L ID) [(L ID, Kind)] [CtorDecl]

data CtorDecl = CtorDecl (L ID) [Type]


data Term
  -- an identifer (variable or ctor or primop, etc.)
  = TmNameOcc (L ID)
  -- \ (x:t) -> e
  | TmLam (L ID) Type Term
  -- e1 e2
  | TmApp Term Term
  -- (e1, e2)
  | TmPair Term Term
  -- fst e
  | TmFst Term
  -- snd e
  | TmSnd Term
  -- e #field
  | TmFieldProj Term FieldLabel
  -- { l1 = e1, ..., ln = en }
  | TmRecord [(FieldLabel, Term)]
  -- let type x:k = t in e
  | TmTypeAlias (L ID) Kind Type Term
  -- let x:t = e1 in e2
  | TmLet (L ID) Type Term Term
  -- let rec (x:t = e)+ in e'
  | TmLetRec [(L ID, Type, Term)] Term
  -- ()
  | TmNil
  -- 17
  | TmInt Int
  -- true, false
  | TmBool Bool
  -- if c return s then t else f
  | TmIf Term Type Term Term
  -- e1 `op` e2
  | TmArith Term TmArith Term
  -- - e1
  | TmNegate Term
  -- e1 `cmp` e2
  | TmCmp Term TmCmp Term
  -- \ @(a : k) -> e
  | TmTLam (L ID) Kind Term
  -- e @s
  | TmTApp Term Type
  -- "foo"
  | TmString String
  -- 'x'
  | TmChar Char
  -- e1 `stringOp` e2
  | TmStringOp Term TmStringOp Term
  -- string_length# e1
  | TmStringLength Term
  -- case e return s of { (c_i (x:t)+ -> e_i')+ }
  | TmCase Term Type [(L ID, [(L ID, Type)], Term)]
  -- pure e
  | TmPure Term
  -- let x : t <- e1 in e2
  | TmBind (L ID) Type Term Term
  -- getLine
  | TmGetLine
  -- putLine e
  | TmPutLine Term
  -- runIO e
  | TmRunIO Term

data TmArith
  = TmArithAdd
  | TmArithSub
  | TmArithMul

data TmCmp
  = TmCmpEq
  | TmCmpNe
  | TmCmpLt
  | TmCmpLe
  | TmCmpGt
  | TmCmpGe
  | TmCmpEqChar

data TmStringOp
  = TmConcat
  | TmIndexStr

data Type
  = TyUnit
  | TyInt
  | TyBool
  | TyString
  | TyChar
  | TyProd Type Type
  | TyArr Type Type
  | TyApp Type Type
  | TyRecord [(FieldLabel, Type)]
  | TyIO Type
  | TyNameOcc (L ID)
  | TyAll (L ID) Kind Type

data Kind
  = KiStar
  | KiArr Kind Kind
  deriving (Eq)



pprintError :: ResolveError -> String
pprintError (NameNotInScope l x) = displayLoc l ++ ": name not in scope: " ++ show x
pprintError (AmbiguousName l x) = displayLoc l ++ ": ambiguous name: " ++ show x
pprintError (DuplicateBinder l l' x) = "multiple binders with same name: " ++ show x
pprintError (UnderAppliedSynonym l x nparams nargs) =
  displayLoc l ++ ": underapplied type synonym: " ++ show x ++ " expects " ++ show nparams ++ " arguments but got " ++ show nargs ++ " arguments"

-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType _ TyUnit = "unit"
pprintType _ TyBool = "bool"
pprintType _ TyInt = "int"
pprintType _ TyString = "string"
pprintType _ TyChar = "char"
pprintType _ (TyRecord []) = "{}"
pprintType _ (TyRecord fs) = "{ " ++ intercalate ", " (map pprintField fs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintType 0 t
-- infixr 4 ->
pprintType p (TyArr t1 t2) = parensIf (p > 4) $ pprintType 5 t1 ++ " -> " ++ pprintType 4 t2
-- infix 5 *
pprintType p (TyProd t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " * " ++ pprintType 6 t2
-- infixl 10 __
pprintType p (TyApp t1 t2) = parensIf (p > 10) $ pprintType 10 t1 ++ " " ++ pprintType 11 t2
pprintType p (TyIO t1) = parensIf (p > 10) $ "IO " ++ pprintType 11 t1
pprintType _ (TyNameOcc x) = show x
pprintType p (TyAll x ki t) =
  parensIf (p > 0) $ "forall (" ++ show x ++ " : " ++ pprintKind ki ++ "). " ++ pprintType 0 t

-- TODO: Decide textual representation for kind of inhabited types: '*' is
-- ambiguous with product.
pprintKind :: Kind -> String
pprintKind KiStar = "*"
pprintKind (KiArr KiStar k2) = "* -> " ++ pprintKind k2
pprintKind (KiArr k1 k2) = "(" ++ pprintKind k1 ++ ") -> " ++ pprintKind k2

parensIf :: Bool -> String -> String
parensIf True x = "(" ++ x ++ ")"
parensIf False x = x


