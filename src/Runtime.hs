module Runtime where

-- Based on [Making a Fast Curry: Push/Enter versus Eval/Apply]

import qualified Data.Map as Map
import Data.Map (Map)

import Data.List.NonEmpty (NonEmpty(..))

data Var = Var String -- Probably not?
  deriving (Eq, Ord)

data Con = Con String
  deriving Eq

data PrimOp = PrimPlusInt

data Lit = LInt Int | LDouble Double

data Atom = ALit Lit | AVar Var

data Arity = Unknown | Known Int

data Expr
  = EAtom Atom
  | EApp Var Arity [Atom]
  | EPrim PrimOp [Atom]
  | ELet Var Obj Expr
  | ECase Expr (Maybe DefAlt) [Alt]

data Alt = Alt Con [Var] Expr
data DefAlt = DefAlt Var Expr -- Pun.

data Obj
  = FUN [Var] Expr
  | PAP Var [Atom] -- Variable points to a 'FUN' object with arity greater than length of atoms
  | CON Con [Atom]
  | THUNK Expr
  | BLACKHOLE

data Program = Program [(Var, Obj)]


isValue :: Obj -> Bool
isValue (FUN _ _) = True
isValue (PAP _ _) = True
isValue (CON _ _) = True
isValue (THUNK _) = False
isValue BLACKHOLE = False


data State = State { code :: Expr, stack :: [Cont], heap :: Heap }

type Heap = Map Var Obj

-- | Allocate a new object on the heap, returning an updated heap and a
-- reference to the object.
alloc :: Heap -> Obj -> (Var, Heap)
alloc h o = (x, h')
  where
    x = Var ("@" ++ show (Map.size h)) -- Note: This works only if the heap doesn't shrink.
    h' = Map.insert x o h

-- | Dereference a heap reference.
deref :: Heap -> Var -> Obj
deref h x = case Map.lookup x h of
  Nothing -> error "bad heap reference"
  Just o -> o

-- | Make @x@ point to a black hole.
blackhole :: Heap -> Var -> Heap
blackhole h x = Map.insert x BLACKHOLE h

-- | Make @x@ point to @H[y]@.
update :: Heap -> Var -> Var -> Heap
update h x y = Map.insert x (deref h y) h

data Cont
  = KCase (Maybe DefAlt) [Alt]
  | KUpd Var -- Var refers a thunk, that will be overwritten with the result.
  | KCall [Atom]


step :: State -> State
-- Rule [PrimOp]
step (State (EPrim p as) s h) = State (EAtom (primOp p as)) s h
-- Rule [Let]
step (State (ELet x o e) s h) = State e' s h'
  where
    (x', h') = alloc h o
    e' = subst x (AVar x') e
-- Rule [CaseCon] and [CaseAny]
step (State (ECase (EAtom a) def alts) s h) = case a of
  ALit _ -> State (takeDefAlt a def) s h
  AVar v -> case deref h v of
    CON c as -> case lookupCon c as alts of
      Nothing -> State (takeDefAlt a def) s h
      Just e' -> State e' s h
    _ -> State (takeDefAlt a def) s h
-- Rule [Case]
step (State (ECase e def alts) s h) = State e (KCase def alts : s) h
-- Rule [Ret], [Thunk]
step (State e@(EAtom a) (KCase def alts : s) h) = case a of
  ALit _ -> State (ECase e def alts) s h
  AVar x -> case deref h x of
    -- [Ret]
    FUN _ _ -> State (ECase e def alts) s h
    PAP _ _ -> State (ECase e def alts) s h
    CON _ _ -> State (ECase e def alts) s h
    -- [Thunk]
    THUNK e' -> State e' (KUpd x : s) (blackhole h x)
    BLACKHOLE -> error "returning a blackhole" -- error? Probably
-- Rule [Update]
step (State e@(EAtom a) (KUpd x : s) h) = case a of
  ALit _ -> error "cannot update literal"
  AVar y -> case deref h x of
    FUN _ _ -> State e s (update h x y)
    PAP _ _ -> State e s (update h x y)
    CON _ _ -> State e s (update h x y)
    THUNK _ -> undefined -- force or error? (not update, because H[y] is required to be a value for that.
    BLACKHOLE -> error "cannot update: still blackhole"
-- Rule [RetFun]
step (State e@(EAtom a) (KCall as : s) h) = case a of
  ALit _ -> error "cannot call literal"
  AVar f -> case deref h f of
    FUN _ _ -> State (EApp f Unknown as) s h
    PAP _ _ -> State (EApp f Unknown as) s h
    _ -> error "cannot call this"
step (State (EApp f (Known n) as) s h) = case deref h f of
  FUN xs e -> case compare (length xs) n of
    -- Rule [KnownCall]
    EQ -> undefined
    -- Rule [PAP2]
    LT -> undefined
    -- Rule [CallK]
    GT -> undefined
  -- Rule [TCall] Hey wait, this only applies to unknown-arity applications.
  THUNK _ -> State (EAtom (AVar f)) (KCall as : s) h
  -- Rule [PCall]
  PAP g as' -> undefined
  _ -> error "call non-function"


takeDefAlt :: Atom -> Maybe DefAlt -> Expr
takeDefAlt a (Just (DefAlt x e)) = subst x a e
takeDefAlt a Nothing = error "bad pattern-match"

lookupCon :: Con -> [Atom] -> [Alt] -> Maybe Expr
lookupCon c as [] = Nothing
lookupCon c as (Alt c' xs e : alts) =
  if c == c' then Just (subst' xs as e) else lookupCon c as alts


primOp :: PrimOp -> [Atom] -> Atom
primOp PrimPlusInt [ALit (LInt x), ALit (LInt y)] = ALit (LInt (x + y))
primOp PrimPlusInt _ = error "bad PrimPlusInt"


subst :: Var -> Atom -> Expr -> Expr
subst x a e = undefined

subst' :: [Var] -> [Atom] -> Expr -> Expr
subst' xs as e = undefined



-- nil = CON "Nil"
-- map = FUN(f, xs -> case xs of {
--   Nil -> nil;
--   Cons y ys ->
--     let h = THUNK (f y);
--         t = THUNK (map f ys);
--         r = CON "Cons" h t
--     in r
-- })
mapProg :: Program
mapProg = Program [
    (Var "nil", CON (Con "Nil") [])
  , (Var "map", FUN [Var "f", Var "xs"] (
    ECase (EAtom (AVar (Var "xs"))) Nothing [
      Alt (Con "Nil") [] (EAtom (AVar (Var "nil")))
    , Alt (Con "Cons") [Var "y", Var "ys"] undefined
    ]
  ))
  ]
