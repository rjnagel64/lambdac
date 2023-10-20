
module CPS.Uncurry (uncurryProgram) where

import CPS.IR

import Control.Monad.Reader
import qualified Data.Set as Set
import Data.Set (Set)


-- Maybe it would be easier to start with a "dead parameter elimination" pass.
-- Eh, whatever.


-- Note: This pass is not terribly effective in absence of inlining. This is
-- because the wrapper is left in place and not propagated, so it basically
-- just adds another layer of indirection.

-- TODO: Make uncurrying work in all scenarios
-- (Right now, it barely works in simple cases, let alone things like:
-- * multiple functions in one bind group
-- * repeated uncurrying (\x -> \y -> \z -> e)
-- * mutual recursion (even <-> odd, etc.)
-- * probably other cases too)


-- Uncurrying as a program transformation:
-- =======================================
--
-- CPS transformation produces a particular pattern of nested function
-- definitions that applies arguments one at a time, creating many intermediate
-- closures.
--
-- This pass seeks to identify nested function definitions created by currying
-- and turn them into an n-argument worker with a number of wrappers.
--
-- let fun f x+ k =
--   let fun g y+ = e1
--   in
--   k g
-- in
-- e2
-- ===>
-- let fun f_worker (x+, y+) =
--   e1
-- in
-- let fun f x+ k =
--   let fun g y+ = f' (x+, y+)
--   in
--   k g
-- in
-- e2
-- provided that g not in FV(e1) and k not in FV(e1)
--
-- The side condition ensures that the inner function 'g' is non-recursive, and
-- that it doesn't make use of the outer continuation. This lets us hoist 'e1'
-- out into a worker function outside of 'f'.
--
-- Note: the argument list 'g y+' includes both the term and continuation
-- arguments of 'g'.
-- See [docs/uncurrying.txt] for more detail


uncurryProgram :: Program -> Program
uncurryProgram (Program ds e) = runM $ Program ds <$> uncurryTerm e

uncurryTerm :: TermK -> M TermK
uncurryTerm (LetFunK fs e) = do
  fs' <- traverse rewriteFunction fs
  LetFunK (concat fs') <$> uncurryTerm e
-- uncurryTerm (LetFunK [f] e) = rewriteFunction f >>= \case
--   Nothing -> LetFunK [f] (uncurryTerm e)
--   Just (fwork, fwrap) -> LetFunK [fwork, fwrap] <$> uncurryTerm e
  -- I should handle multiple functions in the same bind group.
-- Continuations cannot be uncurried.
uncurryTerm (LetContK ks e) = LetContK ks <$> uncurryTerm e -- hmm. Should recurse on ks.
uncurryTerm (LetValK x t v e) = LetValK x t v <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (LetFstK x t y e) = LetFstK x t y <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (LetSndK x t y e) = LetSndK x t y <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (LetFieldK x t y l e) = LetFieldK x t y l <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (LetArithK x op e) = LetArithK x op <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (LetCompareK x op e) = LetCompareK x op <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (LetStringOpK x t op e) = LetStringOpK x t op <$> (withTmBind x $ uncurryTerm e)
uncurryTerm (HaltK x) = pure (HaltK x)
uncurryTerm (JumpK k xs) = pure (JumpK k xs)
-- The fact that we leave behind a wrapper means that we don't need to modify
-- call sites.
-- (But we could if we wanted -- maintain a set of unfoldings for the wrappers,
-- and inline them at call nodes?)
uncurryTerm (CallK f xs ks) = pure (CallK f xs ks)
uncurryTerm (IfK x k1 k2) = IfK x <$> uncurryContDef k1 <*> uncurryContDef k2

uncurryContDef :: ContDef -> M ContDef
uncurryContDef (ContDef xs e) = ContDef xs <$> (withTmBinds xs $ uncurryTerm e)

-- I need a fresh name supply, to generate names for the worker.

-- Hrrm. I cannot mix term and type arguments. These need to be separate code paths.
-- TODO: Return (FunDef, [FunDef]) (worker + wrappers, or wrapper + workers?)
-- Or Way FunDef FunDef: list of workers followed by wrapper at the tail
rewriteFunction :: FunDef -> M [FunDef]
rewriteFunction def@(FunDef f xs [(k, s)] e) = case e of
  LetFunK [FunDef g ys ks body] (JumpK k' [g']) ->
    if k == k' && g == g' then
      let mustAvoid = (Avoid (Set.singleton g) (Set.singleton k) Set.empty) in
      if termAvoids mustAvoid body then do
        -- fwork <- freshTm
        let fwork = case f of TmVar f' i -> TmVar (f' ++ "_worker") i
        -- I should recurse here.
        -- Hmm. I think doing so would mean returning multiple workers/wrappers.
        let worker = FunDef fwork (xs ++ ys) ks body
        let
          argFor (ValueParam x s) = ValueArg x
          argFor (TypeParam aa k) = TypeArg (TyVarOccK aa)
        let coArgFor (k', _) = CoVarK k'
        let wrapper = FunDef f xs [(k, s)] (LetFunK [FunDef g ys ks (CallK fwork (argFor <$> (xs ++ ys)) (coArgFor <$> ks))] (JumpK k [g]))
        pure [worker, wrapper]
      else
        -- Occurs check fails: functions do not have form required by uncurrying.
        pure [def]
    else
      -- Not a nested function definition
      pure [def]
  -- inner definition has too many functions or body is not returning the inner closure
  _ -> pure [def]
-- No continuation: wat.
-- ... This indicates that the partial application does not return?
rewriteFunction def@(FunDef f xs [] e) = pure [def]
-- Too many continuations: this the translation of a curried function.
-- In particular, multiple continuations happen when the continuation accepts a
-- sum type.
-- The continuation of a curried function should accept a function type
-- instead, so we should not end up with multiple continuations.
rewriteFunction def@(FunDef f xs ks e) = pure [def]


-- data CurriedFunDef = _
--
-- workerForFunDef :: CurriedFunDef -> FunDef
-- workerForFunDef (CurriedFunDef f xs ys ks body) =
--   let fwork = freshTm f in
--   _
--
-- wrapperForFunDef :: CurriedFunDef -> FunDef
-- wrapperForFunDef _ = _
--
-- -- The essence of many program optimizations is pattern matching for a
-- -- particular shape, followed by rewriting that occurrence.
-- --
-- -- In particular, we are looking for chains of curried functions, and rewriting
-- -- to a wrapper and an uncurried worker.
-- matchCurriedFunction :: FunDef -> Maybe CurriedFunDef
-- matchCurriedFunction (FunDef f xs [k] e) = case e of
--   LetFunK [FunDef g ys ks body] (JumpK k' [g']) ->
--     if k == k' && g == g' then
--       if termAvoids mustAvoid body then
--         -- Hmm. This gives the worker.
--         -- What about the wrapper?
--         Just (CurriedFunDef f xs ys ks body)



data Avoid = Avoid (Set TmVar) (Set CoVar) (Set TyVar)

-- Assert that the given names do not appear free in a TermK
termAvoids :: Avoid -> TermK -> Bool
termAvoids av (LetValK x t v e) = typeAvoids av t && valueAvoids av v && termAvoids (bindTm x av) e
termAvoids av (LetFstK x t y e) = typeAvoids av t && avoidTmVar av y && termAvoids (bindTm x av) e
termAvoids av (LetSndK x t y e) = typeAvoids av t && avoidTmVar av y && termAvoids (bindTm x av) e
termAvoids av (LetArithK x op e) = arithAvoids av op && termAvoids (bindTm x av) e
termAvoids av (LetCompareK x op e) = cmpAvoids av op && termAvoids (bindTm x av) e
termAvoids av (LetStringOpK x t op e) = typeAvoids av t && stringOpAvoids av op && termAvoids (bindTm x av) e
termAvoids av (LetBindK x y op e) = primIOAvoids av op && termAvoids (bindTm y (bindTm x av)) e
termAvoids av (LetContK ks e) = all (contDefAvoids av . snd) ks && termAvoids av' e
  where av' = foldr bindCo av (map fst ks)
termAvoids av (LetFunK fs e) = all (funDefAvoids av) fs && termAvoids av' e
  where av' = foldr bindTm av (map funDefName fs)
termAvoids av (JumpK k xs) = avoidCoVar av k && all (avoidTmVar av) xs
termAvoids av (CallK f xs ks) = avoidTmVar av f && all (avoidArgument av) xs && all (coValueAvoids av) ks
termAvoids av (IfK x k1 k2) = avoidTmVar av x && contDefAvoids av k1 && contDefAvoids av k2
termAvoids av (CaseK x tcapp alts) = avoidTmVar av x && typeAvoids av (fromTyConApp tcapp) && all (altAvoids av) alts
termAvoids av (HaltK x) = avoidTmVar av x

arithAvoids :: Avoid -> ArithK -> Bool
arithAvoids av (AddK x y) = avoidTmVar av x && avoidTmVar av y
arithAvoids av (SubK x y) = avoidTmVar av x && avoidTmVar av y
arithAvoids av (MulK x y) = avoidTmVar av x && avoidTmVar av y
arithAvoids av (NegK x) = avoidTmVar av x

cmpAvoids :: Avoid -> CmpK -> Bool
cmpAvoids av (CmpEqK x y) = avoidTmVar av x && avoidTmVar av y
cmpAvoids av (CmpNeK x y) = avoidTmVar av x && avoidTmVar av y
cmpAvoids av (CmpLtK x y) = avoidTmVar av x && avoidTmVar av y
cmpAvoids av (CmpLeK x y) = avoidTmVar av x && avoidTmVar av y
cmpAvoids av (CmpGtK x y) = avoidTmVar av x && avoidTmVar av y
cmpAvoids av (CmpGeK x y) = avoidTmVar av x && avoidTmVar av y
cmpAvoids av (CmpEqCharK x y) = avoidTmVar av x && avoidTmVar av y

stringOpAvoids :: Avoid -> StringOpK -> Bool
stringOpAvoids av (ConcatK x y) = avoidTmVar av x && avoidTmVar av y
stringOpAvoids av (IndexK x y) = avoidTmVar av x && avoidTmVar av y
stringOpAvoids av (LengthK x) = avoidTmVar av x

altAvoids :: Avoid -> (Ctor, CoValueK) -> Bool
altAvoids av (_, cv) = coValueAvoids av cv

primIOAvoids :: Avoid -> PrimIO -> Bool
primIOAvoids av (PrimGetLine x) = avoidTmVar av x
primIOAvoids av (PrimPutLine x y) = avoidTmVar av x && avoidTmVar av y

-- Assert that the given names do not appear free in a ValueK
valueAvoids :: Avoid -> ValueK -> Bool
valueAvoids av (VarValK x) = avoidTmVar av x
valueAvoids _ NilValK = True
valueAvoids _ TokenValK = True
valueAvoids av (PairValK x y) = valueAvoids av x && valueAvoids av y
valueAvoids _ (IntValK _) = True
valueAvoids _ (BoolValK _) = True
valueAvoids _ (StringValK _) = True
valueAvoids _ (CharValK _) = True
valueAvoids av (CtorValK _ ts xs) = all (typeAvoids av) ts && all (valueAvoids av) xs

-- Assert that the given names do not appear free in a CoValueK
coValueAvoids :: Avoid -> CoValueK -> Bool
coValueAvoids av (CoVarK k) = avoidCoVar av k
coValueAvoids av (ContValK cont) = contDefAvoids av cont

contDefAvoids :: Avoid -> ContDef -> Bool
contDefAvoids av (ContDef xs e) = termAvoids av' e
  where av' = foldr (\ (x, t) avoid -> bindTm x avoid) av xs

typeAvoids :: Avoid -> TypeK -> Bool
typeAvoids _ UnitK = True
typeAvoids _ TokenK = True
typeAvoids _ IntK = True
typeAvoids _ BoolK = True
typeAvoids _ StringK = True
typeAvoids _ CharK = True
typeAvoids av (ProdK t1 t2) = typeAvoids av t1 && typeAvoids av t2
typeAvoids av (RecordK fs) = all (typeAvoids av) [t | (_, t) <- fs]
typeAvoids av (FunK ts ss) = case teleAvoids av ts of
  Nothing -> False
  Just av' -> all (coTypeAvoids av) ss
typeAvoids av (TyVarOccK aa) = avoidTyVar av aa
typeAvoids _ (TyConOccK _) = True
typeAvoids av (TyAppK t1 t2) = typeAvoids av t1 && typeAvoids av t2

teleAvoids :: Avoid -> [TeleEntry] -> Maybe Avoid
teleAvoids av [] = Just av
teleAvoids av (ValueTele t : ts) = if typeAvoids av t then teleAvoids av ts else Nothing
teleAvoids av (TypeTele aa k : ts) = teleAvoids (bindTy aa av) ts

coTypeAvoids :: Avoid -> CoTypeK -> Bool
coTypeAvoids av (ContK ts) = all (typeAvoids av) ts

funDefAvoids :: Avoid -> FunDef -> Bool
funDefAvoids av (FunDef f xs ks e) = case paramsAvoid (bindTm f av) xs of
  Nothing -> False
  Just av' -> case coParamsAvoid av' ks of
    Nothing -> False
    Just av'' -> termAvoids av'' e

paramsAvoid :: Avoid -> [FunParam] -> Maybe Avoid
paramsAvoid av [] = Just av
paramsAvoid av (ValueParam x t : xs) = if typeAvoids av t then paramsAvoid (bindTm x av) xs else Nothing
paramsAvoid av (TypeParam aa _k : xs) = paramsAvoid (bindTy aa av) xs

coParamsAvoid :: Avoid -> [(CoVar, CoTypeK)] -> Maybe Avoid
coParamsAvoid av [] = Just av
coParamsAvoid av ((k, s) : ks) = if coTypeAvoids av s then coParamsAvoid (bindCo k av) ks else Nothing


avoidArgument :: Avoid -> Argument -> Bool
avoidArgument av (ValueArg x) = avoidTmVar av x
avoidArgument av (TypeArg t) = typeAvoids av t

avoidTmVar :: Avoid -> TmVar -> Bool
avoidTmVar (Avoid xs _ _) x = Set.notMember x xs

avoidCoVar :: Avoid -> CoVar -> Bool
avoidCoVar (Avoid _ ks _) k = Set.notMember k ks

avoidTyVar :: Avoid -> TyVar -> Bool
avoidTyVar (Avoid _ _ as) aa = Set.notMember aa as

bindTm :: TmVar -> Avoid -> Avoid
bindTm x (Avoid xs ks as) = Avoid (Set.delete x xs) ks as

bindCo :: CoVar -> Avoid -> Avoid
bindCo k (Avoid xs ks as) = Avoid xs (Set.delete k ks) as

bindTy :: TyVar -> Avoid -> Avoid
bindTy aa (Avoid xs ks as) = Avoid xs ks (Set.delete aa as)


newtype M a = M { getM :: Reader InScopeSet a }

data InScopeSet = InScopeSet (Set TmVar)

emptyScope :: InScopeSet
emptyScope = InScopeSet Set.empty

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader InScopeSet M

-- Hrrm. I need some sort of name supply. In particular, I need to create
-- (possibly multiple) new names in the middle of a recursive bind group, which
-- is messy.
-- Arbitrary gensyms? Maybe. Might run into problems if there are pre-existing
-- gensyms in the program, though.
-- (I.E., running uncurrying twice might try to generate the same gensym in the
-- same bindgroup, which would lead to problems.)
--
-- Alternatively, I can do the whole 'Reader InScopeSet' thing, but that
-- doesn't play all that nicely with the fact that I need to create new names
-- in the middle of a bind group.
--
-- 'State InScopeSet' is just as bad, because you have to manually remove
-- things from scope.
--
-- So maybe, Reader InScopeSet, but with particular combinators for threading a
-- mutable InScopeSet through a bind group (and putting it back for recursive
-- calls?) Maybe.
runM :: M a -> a
runM m = flip runReader emptyScope (getM m)



-- bring a term variable into scope
withTmBind :: TmVar -> M a -> M a
withTmBind x cont = local extend cont
  where
    extend (InScopeSet xs) = InScopeSet (Set.insert x xs)

withTmBinds :: [(TmVar, TypeK)] -> M a -> M a
withTmBinds [] m = m
withTmBinds ((x, _t) : xs) m = withTmBind x $ withTmBinds xs m

-- generate a fresh name, extending the scope with it
withFreshTm :: (TmVar -> M a) -> M a
withFreshTm cont = do
  InScopeSet sc <- ask
  let x = go 0 sc
  local (\ (InScopeSet sc) -> InScopeSet (Set.insert x sc)) $ cont x
  where
    go i sc = let x = TmVar "x" i in if Set.member x sc then go (i+1) sc else x

