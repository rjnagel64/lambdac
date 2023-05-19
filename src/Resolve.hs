
module Resolve
  ( resolveProgram
  , Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmStringOp(..)
  , ID(..)
  , Type(..)
  , TyVar(..)
  , Kind(..)
  , FieldLabel(..)

  , TyCon(..)
  , Program(..)
  , DataDecl(..)
  , CtorDecl(..)

  , pprintType
  , pprintKind
  ) where

import Data.List (intercalate)
import Data.Traversable (for)

import qualified Source.IR as S

import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)


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
  assertDistinctIDs [c | CtorDecl c _ <- ctors]

  (binds, ctors') <- fmap unzip . for ctors $ \ (CtorDecl c@(ID ident) args) -> do
    let c' = S.Ctor ident
    withTyVars as $ \as' -> do
      args' <- traverse resolveType args
      pure ((c, c'), S.CtorDecl c' args') -- I should include the as' in the new ctor decl

  let extend env = env { ctxCons = insertMany binds (ctxCons env) }
  local extend $ cont ctors'

assertDistinctIDs :: [ID] -> M ()
assertDistinctIDs xs = pure ()

withRecBinds :: [(ID, Type, Term)] -> ([(S.TmVar, S.Type, S.Term)] -> M a) -> M a
withRecBinds xs cont = do
  assertDistinctIDs [x | (x, _, _) <- xs]

  (binds, ys) <- fmap unzip . for xs $ \ (x@(ID ident), t, e) -> do
    let x' = S.TmVar ident
    t' <- resolveType t
    pure ((x, x'), (x', t', e))

  let extend env = env { ctxVars = insertMany binds (ctxVars env) }
  local extend $ do
    xs' <- for ys $ \ (x', t', e) -> do
      e' <- resolveTerm e
      pure (x', t', e')
    cont xs'

resolveTerm :: Term -> M S.Term
resolveTerm (TmNameOcc (ID x)) = do
  tmVarEnv <- asks ctxVars
  ctorEnv <- asks ctxCons
  case (Map.lookup (ID x) tmVarEnv, Map.lookup (ID x) ctorEnv) of
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
  alts' <- for alts $ \ (ID c, xs, rhs) -> do
    envCtors <- asks ctxCons
    c' <- case Map.lookup (ID c) envCtors of
      Nothing -> error ("ctor not in scope: " ++ c)
      Just c' -> pure c'
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
resolveType (TyNameOcc (ID x)) = do
  tyVars <- asks ctxTyVars
  tyCons <- asks ctxTyCons
  case (Map.lookup (TyVar x) tyVars, Map.lookup (TyCon x) tyCons) of
    (Nothing, Nothing) -> error ("name not in scope: " ++ x)
    (Just x', Nothing) -> pure (S.TyVarOcc x')
    (Nothing, Just x') -> pure (S.TyConOcc x')
    (Just _, Just _) -> error ("abiguous name (could be tyvar or tycon") 
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

withTmVar :: ID -> Type -> (S.TmVar -> S.Type -> M a) -> M a
withTmVar x@(ID ident) t cont = do
  let x' = S.TmVar ident
  t' <- resolveType t
  let extend env = env { ctxVars = Map.insert x x' (ctxVars env) }
  local extend $ cont x' t'

withTmVars :: [(ID, Type)] -> ([(S.TmVar, S.Type)] -> M a) -> M a
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
    ctxVars :: Map ID S.TmVar
  , ctxCons :: Map ID S.Ctor
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
  deriving (Eq, Ord)

instance Show ID where
  show (ID x) = x

-- TODO: Remove TmVar, TyVar, Ctor, TyCon from Resolve. They should only be in Source

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

newtype FieldLabel = FieldLabel String
  deriving (Eq)

instance Show FieldLabel where
  show (FieldLabel f) = f


data Program = Program [DataDecl] Term


data DataDecl = DataDecl TyCon [(TyVar, Kind)] [CtorDecl]

data CtorDecl = CtorDecl ID [Type]


data Term
  -- an identifer (variable or ctor or primop, etc.)
  = TmNameOcc ID
  -- \ (x:t) -> e
  | TmLam ID Type Term
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
  | TmLet ID Type Term Term
  -- let rec (x:t = e)+ in e'
  | TmLetRec [(ID, Type, Term)] Term
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
  | TmCase Term Type [(ID, [(ID, Type)], Term)]
  -- pure e
  | TmPure Term
  -- let x : t <- e1 in e2
  | TmBind ID Type Term Term
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
  | TyNameOcc ID
  | TyAll TyVar Kind Type

data Kind
  = KiStar
  | KiArr Kind Kind
  deriving (Eq)



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


