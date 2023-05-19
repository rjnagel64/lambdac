
module Resolve
  ( resolveProgram
  , Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmStringOp(..)
  , ID(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)
  , Kind(..)
  , FieldLabel(..)

  , eqType
  , Subst
  , singleSubst
  , makeSubst
  , substType
  , ftv

  , TyCon(..)
  , Ctor(..)
  , Program(..)
  , DataDecl(..)
  , CtorDecl(..)

  , pprintType
  , pprintKind
  ) where

-- * duplicate syntax of Source IR
-- * define no-op name-resolution pass to Source
-- * rewire driver to pass through Resolve
-- * Start refactoring Resolve IR to take ID for all identifiers, resolve based
--   on usage.

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Bifunctor
import Data.List (intercalate)
import Data.Traversable (for)

import qualified Source as S

import Control.Monad.Reader


-- | Utility function for inserting many items at once.
insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs


resolveProgram :: Program -> S.Program
resolveProgram (Program ds e) = runM $ do
  withDataDecls ds $ \ds' -> do
    e' <- resolveTerm e
    pure (S.Program ds' e')

withDataDecls :: [DataDecl] -> ([S.DataDecl] -> M a) -> M a
withDataDecls [] cont = cont []
withDataDecls (d:ds) cont = withDataDecl d $ \d' -> withDataDecls ds $ \ds' -> cont (d':ds')

withDataDecl :: DataDecl -> (S.DataDecl -> M a) -> M a
withDataDecl (DataDecl tc as ctors) cont = do
  let k = foldr KiArr KiStar (map snd as)
  withTyCon tc k $ \tc' k' -> do
    -- bring group of ctors into scope, in parallel
    withCtors as ctors $ \ctors' -> do
      -- kind of hacky. It would be better for Source and subsequent IRs to be
      -- like GADTs, with the data decl having a kind signature, but the tyvars
      -- being confined to each constructor.
      as' <- traverse (\ (TyVar a, k) -> (,) <$> pure (S.TyVar a) <*> resolveKind k) as
      cont (S.DataDecl tc' as' ctors')

-- bring a set of constructors into scope, in parallel.
withCtors :: [(TyVar, Kind)] -> [CtorDecl] -> ([S.CtorDecl] -> M a) -> M a
withCtors as ctors cont = do
  assertDistinctCtors [c | CtorDecl c _ <- ctors]

  (binds, ctors') <- fmap unzip . for ctors $ \ (CtorDecl c@(Ctor ident) args) -> do
    let c' = S.Ctor ident
    withTyVars as $ \as' -> do
      args' <- traverse resolveType args
      pure ((c, c'), S.CtorDecl c' args') -- I should include the as' in the new ctor decl

  let extend env = env { ctxCons = insertMany binds (ctxCons env) }
  local extend $ cont ctors'

assertDistinctCtors :: [Ctor] -> M ()
assertDistinctCtors cs = pure () -- TODO: detect duplicates

withRecBinds :: [(TmVar, Type, Term)] -> ([(S.TmVar, S.Type, S.Term)] -> M a) -> M a
withRecBinds xs cont = do
  assertDistinctTmVars [x | (x, _, _) <- xs]

  (binds, ys) <- fmap unzip . for xs $ \ (x@(TmVar ident), t, e) -> do
    let x' = S.TmVar ident
    t' <- resolveType t
    pure ((x, x'), (x', t', e))

  let extend env = env { ctxVars = insertMany binds (ctxVars env) }
  local extend $ do
    xs' <- for ys $ \ (x', t', e) -> do
      e' <- resolveTerm e
      pure (x', t', e')
    cont xs'

assertDistinctTmVars :: [TmVar] -> M ()
assertDistinctTmVars xs = pure () -- TODO: detect duplicates

resolveTerm :: Term -> M S.Term
resolveTerm (TmNameOcc (ID x)) = do
  tmVarEnv <- asks ctxVars
  ctorEnv <- asks ctxCons
  case (Map.lookup (TmVar x) tmVarEnv, Map.lookup (Ctor x) ctorEnv) of
    -- Hmm. this is an elab-style pass, I should return real errors since they are user-facing.
    (Nothing, Nothing) -> error ("name not in scope: " ++ x)
    (Just x', Nothing) -> pure (S.TmVarOcc x')
    (Nothing, Just x') -> pure (S.TmCtorOcc x')
    (Just _, Just _) -> error "ambiguous name (could be variable or ctor)"
resolveTerm TmNil = pure S.TmNil
resolveTerm TmGetLine = pure S.TmGetLine
resolveTerm (TmInt i) = pure (S.TmInt i)
resolveTerm (TmBool b) = pure (S.TmBool b)
resolveTerm (TmString s) = pure (S.TmString s)
resolveTerm (TmChar c) = pure (S.TmChar c)
resolveTerm (TmPure e) = S.TmPure <$> resolveTerm e
resolveTerm (TmPutLine e) = S.TmPutLine <$> resolveTerm e
resolveTerm (TmRunIO e) = S.TmRunIO <$> resolveTerm e
resolveTerm (TmFst e) = S.TmFst <$> resolveTerm e
resolveTerm (TmSnd e) = S.TmSnd <$> resolveTerm e
resolveTerm (TmFieldProj e l) = S.TmFieldProj <$> resolveTerm e <*> resolveFieldLabel l
resolveTerm (TmPair e1 e2) = S.TmPair <$> resolveTerm e1 <*> resolveTerm e2
resolveTerm (TmRecord fs) = S.TmRecord <$> traverse resolveField fs
  where resolveField (l, e) = (,) <$> resolveFieldLabel l <*> resolveTerm e
resolveTerm (TmArith e1 op e2) =
  S.TmArith <$> resolveTerm e1 <*> resolveArith op <*> resolveTerm e2
resolveTerm (TmNegate e) = S.TmNegate <$> resolveTerm e
resolveTerm (TmCmp e1 op e2) =
  S.TmCmp <$> resolveTerm e1 <*> resolveCmp op <*> resolveTerm e2
resolveTerm (TmStringOp e1 op e2) =
  S.TmStringOp <$> resolveTerm e1 <*> resolveStringOp op <*> resolveTerm e2
resolveTerm (TmApp e1 e2) = S.TmApp <$> resolveTerm e1 <*> resolveTerm e2
resolveTerm (TmTApp e t) = S.TmTApp <$> resolveTerm e <*> resolveType t
resolveTerm (TmLam x t e) = do
  withTmVar x t $ \x' t' -> do
    e' <- resolveTerm e
    pure (S.TmLam x' t' e')
resolveTerm (TmTLam a k e) = do
  withTyVar a k $ \a' k' -> do
    e' <- resolveTerm e
    pure (S.TmTLam a' k' e')
resolveTerm (TmLet x t e1 e2) = do
  e1' <- resolveTerm e1
  withTmVar x t $ \x' t' -> do
    e2' <- resolveTerm e2
    pure (S.TmLet x' t' e1' e2')
resolveTerm (TmBind x t e1 e2) = do
  e1' <- resolveTerm e1
  withTmVar x t $ \x' t' -> do
    e2' <- resolveTerm e2
    pure (S.TmBind x' t' e1' e2')
resolveTerm (TmLetRec xs e) = do
  withRecBinds xs $ \xs' -> do
    e' <- resolveTerm e
    pure (S.TmLetRec xs' e')
resolveTerm (TmCase e s alts) = do
  e' <- resolveTerm e
  s' <- resolveType s
  alts' <- for alts $ \ (c, xs, rhs) -> do
    c' <- resolveCtorOcc c
    withTmVars xs $ \xs' -> do
      rhs' <- resolveTerm rhs
      pure (c', xs', rhs')
  pure (S.TmCase e' s' alts')
resolveTerm (TmIf ec s et ef) = do
  ec' <- resolveTerm ec
  s' <- resolveType s
  et' <- resolveTerm et
  ef' <- resolveTerm ef
  pure (S.TmIf ec' s' et' ef')

resolveType :: Type -> M S.Type
resolveType (TyVarOcc a) = do
  env <- asks ctxTyVars
  case Map.lookup a env of
    Nothing -> error ("tyvar not in scope: " ++ show a)
    Just a' -> pure (S.TyVarOcc a')
resolveType (TyConOcc tc) = do
  env <- asks ctxTyCons
  case Map.lookup tc env of
    Nothing -> error "tycon not in scope"
    Just tc' -> pure (S.TyConOcc tc')
resolveType TyUnit = pure S.TyUnit
resolveType TyInt = pure S.TyInt
resolveType TyBool = pure S.TyBool
resolveType TyString = pure S.TyString
resolveType TyChar = pure S.TyChar
resolveType (TyProd t s) = S.TyProd <$> resolveType t <*> resolveType s
resolveType (TyArr t s) = S.TyArr <$> resolveType t <*> resolveType s
resolveType (TyApp t s) = S.TyApp <$> resolveType t <*> resolveType s
resolveType (TyIO t) = S.TyIO <$> resolveType t
resolveType (TyRecord fs) = S.TyRecord <$> traverse resolveField fs
  where resolveField (l, t) = (,) <$> resolveFieldLabel l <*> resolveType t
resolveType (TyAll a k t) = do
  withTyVar a k $ \a' k' -> do
    t' <- resolveType t
    pure (S.TyAll a' k' t')

resolveKind :: Kind -> M S.Kind
resolveKind KiStar = pure S.KiStar
resolveKind (KiArr k1 k2) = S.KiArr <$> resolveKind k1 <*> resolveKind k2

resolveArith :: TmArith -> M S.TmArith
resolveArith TmArithAdd = pure S.TmArithAdd
resolveArith TmArithSub = pure S.TmArithSub
resolveArith TmArithMul = pure S.TmArithMul

resolveCmp :: TmCmp -> M S.TmCmp
resolveCmp TmCmpEq = pure S.TmCmpEq
resolveCmp TmCmpNe = pure S.TmCmpNe
resolveCmp TmCmpLt = pure S.TmCmpLt
resolveCmp TmCmpLe = pure S.TmCmpLe
resolveCmp TmCmpGt = pure S.TmCmpGt
resolveCmp TmCmpGe = pure S.TmCmpGe
resolveCmp TmCmpEqChar = pure S.TmCmpEqChar

resolveStringOp :: TmStringOp -> M S.TmStringOp
resolveStringOp TmConcat = pure S.TmConcat
resolveStringOp TmIndexStr = pure S.TmIndexStr

resolveFieldLabel :: FieldLabel -> M S.FieldLabel
resolveFieldLabel (FieldLabel l) = pure (S.FieldLabel l)

resolveCtorOcc :: Ctor -> M S.Ctor
resolveCtorOcc c = do
  env <- asks ctxCons
  case Map.lookup c env of
    Nothing -> error "ctor not in scope"
    Just c' -> pure c'

withTmVar :: TmVar -> Type -> (S.TmVar -> S.Type -> M a) -> M a
withTmVar x@(TmVar ident) t cont = do
  let x' = S.TmVar ident
  t' <- resolveType t
  let extend env = env { ctxVars = Map.insert x x' (ctxVars env) }
  local extend $ cont x' t'

withTmVars :: [(TmVar, Type)] -> ([(S.TmVar, S.Type)] -> M a) -> M a
withTmVars [] cont = cont []
withTmVars ((x, t):xs) cont = withTmVar x t $ \x' t' -> withTmVars xs $ \xs' -> cont ((x', t'):xs')

withTyVar :: TyVar -> Kind -> (S.TyVar -> S.Kind -> M a) -> M a
withTyVar a@(TyVar ident) k cont = do
  let a' = S.TyVar ident
  k' <- resolveKind k
  let extend env = env { ctxTyVars = Map.insert a a' (ctxTyVars env) }
  local extend $ cont a' k'

withTyVars :: [(TyVar, Kind)] -> ([(S.TyVar, S.Kind)] -> M a) -> M a
withTyVars [] cont = cont []
withTyVars ((a, k):as) cont = withTyVar a k $ \a' k' -> withTyVars as $ \as' -> cont ((a', k'):as')

withTyCon :: TyCon -> Kind -> (S.TyCon -> S.Kind -> M a) -> M a
withTyCon tc@(TyCon ident) k cont = do
  let tc' = S.TyCon ident
  k' <- resolveKind k
  let extend env = env { ctxTyCons = Map.insert tc tc' (ctxTyCons env) }
  local extend $ cont tc' k'


newtype M a = M { getM :: Reader Context a }

deriving instance Functor M
deriving instance Applicative M
deriving instance Monad M
deriving instance MonadReader Context M

data Context
  = Context {
    ctxVars :: Map TmVar S.TmVar
  , ctxCons :: Map Ctor S.Ctor
  , ctxTyVars :: Map TyVar S.TyVar
  , ctxTyCons :: Map TyCon S.TyCon
  }

runM :: M a -> a
runM = flip runReader emptyContext . getM
  where
    emptyContext = Context {
        ctxVars = Map.empty
      , ctxCons = Map.empty
      , ctxTyVars = Map.empty
      , ctxTyCons = Map.empty
      }


-- | A generic identifier, that will be resolved to an appropriate type by this pass.
newtype ID = ID String


-- | Term variables stand for values.
newtype TmVar = TmVar String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x) = x

-- | Type variables stand for types.
data TyVar
  = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar x) = x


data TyCon = TyCon String
  deriving (Eq, Ord)

instance Show TyCon where
  show (TyCon tc) = tc

data Ctor = Ctor String
  deriving (Eq, Ord)

instance Show Ctor where
  show (Ctor c) = c

newtype FieldLabel = FieldLabel String
  deriving (Eq)

instance Show FieldLabel where
  show (FieldLabel f) = f


data Program = Program [DataDecl] Term


data DataDecl = DataDecl TyCon [(TyVar, Kind)] [CtorDecl]

data CtorDecl = CtorDecl Ctor [Type]


data Term
  -- an identifer (variable or ctor or primop, etc.)
  = TmNameOcc ID
  -- \ (x:t) -> e
  | TmLam TmVar Type Term
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
  -- let x:t = e1 in e2
  | TmLet TmVar Type Term Term
  -- let rec (x:t = e)+ in e'
  | TmLetRec [(TmVar, Type, Term)] Term
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
  | TmTLam TyVar Kind Term
  -- e @s
  | TmTApp Term Type
  -- "foo"
  | TmString String
  -- 'x'
  | TmChar Char
  -- e1 `stringOp` e2
  | TmStringOp Term TmStringOp Term
  -- case e return s of { (c_i (x:t)+ -> e_i')+ }
  | TmCase Term Type [(Ctor, [(TmVar, Type)], Term)]
  -- pure e
  | TmPure Term
  -- let x : t <- e1 in e2
  | TmBind TmVar Type Term Term
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
  -- s1 ^ s2
  = TmConcat
  -- char_at_idx x i
  | TmIndexStr

-- | Named function definitions are one way of doing recursion.
-- (On the other hand, let-rec expressions.)
data TmFun
  -- | @f (x : t) : t' = e@
  = TmFun TmVar TmVar Type Type Term
  -- | @f \@a : t' = e@
  | TmTFun TmVar TyVar Kind Type Term

data Type
  = TyProd Type Type
  | TyRecord [(FieldLabel, Type)]
  | TyArr Type Type
  | TyUnit
  | TyInt
  | TyBool
  | TyVarOcc TyVar
  | TyAll TyVar Kind Type
  | TyString
  | TyChar
  | TyConOcc TyCon
  | TyApp Type Type
  | TyIO Type

instance Eq Type where
  (==) = eqType emptyAE

data Kind
  = KiStar
  | KiArr Kind Kind
  deriving (Eq)


data AE = AE Int (Map TyVar Int) (Map TyVar Int)

emptyAE :: AE
emptyAE = AE 0 Map.empty Map.empty

lookupAE :: AE -> TyVar -> TyVar -> Bool
lookupAE (AE _ fw bw) x y = case (Map.lookup x fw, Map.lookup y bw) of
  -- Both bound: should be bound at the same level
  (Just xl, Just yl) -> xl == yl
  -- Both free: require exact equality
  (Nothing, Nothing) -> x == y
  -- Cannot be equal if one free but the other is bound
  _ -> False

bindAE :: TyVar -> TyVar -> AE -> AE
bindAE x y (AE l fw bw) = AE (l+1) (Map.insert x l fw) (Map.insert y l bw)

-- | Alpha-equality of two types
eqType :: AE -> Type -> Type -> Bool
eqType ae (TyVarOcc x) (TyVarOcc y) = lookupAE ae x y
eqType _ (TyVarOcc _) _ = False
eqType _ (TyConOcc c1) (TyConOcc c2) = c1 == c2
eqType _ (TyConOcc _) _ = False
eqType _ TyUnit TyUnit = True
eqType _ TyUnit _ = False
eqType _ TyBool TyBool = True
eqType _ TyBool _ = False
eqType _ TyInt TyInt = True
eqType _ TyInt _ = False
eqType _ TyString TyString = True
eqType _ TyString _ = False
eqType _ TyChar TyChar = True
eqType _ TyChar _ = False
eqType ae (TyProd t1 t2) (TyProd t3 t4) = eqType ae t1 t3 && eqType ae t2 t4
eqType _ (TyProd _ _) _ = False
eqType ae (TyRecord fs1) (TyRecord fs2) = go fs1 fs2
  where
    go [] [] = True
    go ((f1, t1):fs1') ((f2, t2):fs2') = f1 == f2 && eqType ae t1 t2 && go fs1' fs2'
    go _ _ = False
eqType _ (TyRecord _) _ = False
eqType ae (TyArr arg1 ret1) (TyArr arg2 ret2) =
  eqType ae arg1 arg2 && eqType ae ret1 ret2
eqType _ (TyArr _ _) _ = False
eqType ae (TyApp arg1 ret1) (TyApp arg2 ret2) =
  eqType ae arg1 arg2 && eqType ae ret1 ret2
eqType _ (TyApp _ _) _ = False
eqType ae (TyIO arg1) (TyIO arg2) =
  eqType ae arg1 arg2
eqType _ (TyIO _) _ = False
eqType ae (TyAll x k1 t) (TyAll y k2 s) = k1 == k2 && eqType (bindAE x y ae) t s
eqType _ (TyAll _ _ _) _ = False


data Subst = Subst { substScope :: Set TyVar, substMapping :: Map TyVar Type }

-- | Construct a singleton substitution, @[aa := t]@.
singleSubst :: TyVar -> Type -> Subst
singleSubst aa t = Subst { substScope = ftv t, substMapping = Map.singleton aa t }

makeSubst :: [(TyVar, Type)] -> Subst
makeSubst binds = Subst { substScope = foldMap (ftv . snd) binds, substMapping = Map.fromList binds }

substBind :: Subst -> TyVar -> (Subst, TyVar)
substBind (Subst sc sub) aa =
  if Set.notMember aa sc then
    (Subst (Set.insert aa sc) (Map.delete aa sub), aa)
  else
    go (0 :: Int)
  where
    go i =
      let TyVar aa' = aa in
      let bb = TyVar (aa' ++ show i) in
      if Set.notMember bb sc then
        (Subst (Set.insert bb sc) (Map.insert aa (TyVarOcc bb) sub), bb)
      else
        go (i+1)

substTyVar :: Subst -> TyVar -> Type
substTyVar sub aa = case Map.lookup aa (substMapping sub) of
  Nothing -> TyVarOcc aa
  Just t -> t

-- | Apply a substitution to a type, @substType sub t' === t'[sub]@.
substType :: Subst -> Type -> Type
substType sub (TyVarOcc bb) = substTyVar sub bb
substType sub (TyAll aa ki t) = let (sub', aa') = substBind sub aa in TyAll aa' ki (substType sub' t)
substType _ TyUnit = TyUnit
substType _ TyBool = TyBool
substType _ TyInt = TyInt
substType _ TyString = TyString
substType _ TyChar = TyChar
substType sub (TyProd t1 t2) = TyProd (substType sub t1) (substType sub t2)
substType sub (TyRecord fs) = TyRecord (map (second (substType sub)) fs)
substType sub (TyArr t1 t2) = TyArr (substType sub t1) (substType sub t2)
substType sub (TyApp t1 t2) = TyApp (substType sub t1) (substType sub t2)
substType sub (TyIO t1) = TyIO (substType sub t1)
substType _ (TyConOcc tc) = TyConOcc tc

-- | Compute the free type variables of a type
ftv :: Type -> Set TyVar
ftv (TyVarOcc aa) = Set.singleton aa
ftv (TyAll bb _ t) = Set.delete bb (ftv t)
ftv (TyProd t1 t2) = ftv t1 <> ftv t2
ftv (TyRecord fs) = foldMap (ftv . snd) fs
ftv (TyArr t1 t2) = ftv t1 <> ftv t2
ftv TyUnit = Set.empty
ftv TyBool = Set.empty
ftv TyInt = Set.empty
ftv TyString = Set.empty
ftv TyChar = Set.empty
ftv (TyConOcc _) = Set.empty
ftv (TyApp t1 t2) = ftv t1 <> ftv t2
ftv (TyIO t1) = ftv t1

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
pprintType _ (TyVarOcc x) = show x
pprintType _ (TyConOcc c) = show c
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


