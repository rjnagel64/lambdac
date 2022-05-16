
module Source
  ( Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)
  , pprintType
  ) where

-- TODO: 'Source' level optimizations?
-- At the very least, arity raising/uncurrying is much easier here.
-- (On a related note, maybe support multiple arguments/parameters here, with
-- requirement of exact arity matching. Parser still generates curried
-- functions and applications, but Source and CPS support the uncurried
-- versions as well.)

-- | Term variables stand for values
newtype TmVar = TmVar String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x) = x

-- | Continuation variables name basic blocks and jump targets.
newtype CoVar = CoVar String
  deriving (Eq, Ord)


data Term
  -- x
  = TmVarOcc TmVar
  -- case e return s of inl (x : t1) -> e1; inr (y : t2) -> e2
  -- TODO: Store constructor name at each branch, and later map ctor names to
  -- ctor tags
  | TmCase Term Type (TmVar, Type, Term) (TmVar, Type, Term)
  -- inl @a @b e
  | TmInl Type Type Term
  -- inr @a @b e
  | TmInr Type Type Term
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
  -- let x:t = e1 in e2
  | TmLet TmVar Type Term Term
  -- let rec fs+ in e
  | TmRecFun [TmFun] Term
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


-- @f (x : t) : t' = e@, used for recursion.
-- I'm not really satisfied with this. How does a 'TmFun' interact with polymorphism?
-- How does it deal with multiple parameters? (i.e., if I allow 'TmFun' to have
-- multiple parameters, are unsaturated applications permitted?)
-- What do multiple-argument functions look like after CPS?
--
-- @let fun f x = e; in e'@ is basically @let rec f = \x -> e; in e'@.
-- Mutually recursive functions are the fixpoint of a tuple.
-- @let f1 x1 = e1; f2 x2 = e2; in e'@ is equivalent to
-- @let rec fs = (\x1 -> e1, x2 -> e2); in let f1 = fst fs; f2 = snd fs; in e'@
-- I think that this encoding is inefficient, though. (environment contains
-- tuple instead of pointers to recursive occurrences directly?)
--
-- I think I should add a @let rec@ construct, such as
-- @let rec x1 = e1; x2 = e2; ...; in e'@.
-- This is desirable, because I can make mutually recursive, many-argument,
-- polymorphic functions easily?
-- This level of generality is not desirable, because I have strict evaluation
-- and cyclic values require laziness to not diverge.
-- ... Can I do patching like for closures?
-- value *x1 = alloc_pair(1, NULL);
-- value *x2 = alloc_pair(2, NULL);
-- x1->snd = x2;
-- x2->snd = x1;
--
-- Is there a difference between partially-applied occurrences within
-- definition versus partially-applied occurrences within body?
data TmFun = TmFun TmVar TmVar Type Type Term

data Type
  = TySum Type Type
  | TyProd Type Type
  | TyArr Type Type
  | TyUnit
  | TyInt
  | TyBool
  | TyVarOcc TyVar
  | TyAll TyVar Type

data TyVar
  = TyVar String

instance Show TyVar where
  show (TyVar x) = x

-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType p TyUnit = "unit"
pprintType p TyBool = "bool"
pprintType p TyInt = "int"
-- infixr 4 ->
pprintType p (TyArr t1 t2) = parensIf (p > 4) $ pprintType 5 t1 ++ " -> " ++ pprintType 4 t2
-- infix 5 *
pprintType p (TyProd t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " * " ++ pprintType 6 t2
-- infix 5 +
pprintType p (TySum t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " + " ++ pprintType 6 t2
pprintType p (TyVarOcc x) = show x
pprintType p (TyAll x t) = parensIf (p > 0) $ "forall " ++ show x ++ "." ++ pprintType 0 t

parensIf :: Bool -> String -> String
parensIf True x = "(" ++ x ++ ")"
parensIf False x = x

