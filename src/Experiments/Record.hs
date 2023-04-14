{-# LANGUAGE TypeFamilies #-}

module Experiments.Record where

-- An experiment/prototype of collecting record types in a program, so that
-- they can be monomorphised.
--
-- This is done using a trie data structure.

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.State hiding ((>=>))


(>>>) :: (a -> b) -> (b -> c) -> (a -> c)
f >>> g = \x -> g (f x)

(>=>) :: (a -> Maybe b) -> (b -> Maybe c) -> (a -> Maybe c)
f >=> g = \x -> case f x of { Nothing -> Nothing; Just y -> g y }


data TyVar = TyVar String
  deriving (Eq, Ord, Show)

data Label = Label String
  deriving (Eq, Ord, Show)

data Sort
  = TyVarH TyVar
  | IntegerH
  | ClosureH Tele
  | RecordH Record
  deriving (Show)

data Tele
  = TeleEnd
  | ValueTele Sort Tele
  | TypeTele TyVar Tele
  deriving (Show)

data Record
  = RecEnd
  | RecExtend Label Sort Record
  deriving (Show)

instance AEq Sort where
  aeq ae (TyVarH aa) (TyVarH bb) = lookupAE ae aa bb
  aeq ae IntegerH IntegerH = True
  aeq ae (ClosureH tele1) (ClosureH tele2) = aeq ae tele1 tele2
  aeq ae (RecordH rec1) (RecordH rec2) = aeq ae rec1 rec2
  aeq _ _ _ = False

instance AEq Tele where
  aeq ae TeleEnd TeleEnd = True
  aeq ae (ValueTele s1 t1) (ValueTele s2 t2) = aeq ae s1 s2 && aeq ae t1 t2
  aeq ae (TypeTele aa t1) (TypeTele bb t2) = aeq (extendAE aa bb ae) t1 t2
  aeq _ _ _ = False

instance AEq Record where
  aeq ae RecEnd RecEnd = True
  aeq ae (RecExtend l1 s1 r1) (RecExtend l2 s2 r2) =
    l1 == l2 && aeq ae s1 s2 && aeq ae r1 r2
  aeq _ _ _ = False


type XT v = Maybe v -> Maybe v

class (Traversable tm, Eq (Key tm)) => TrieMap tm where
  type Key tm
  emptyTM :: tm v
  alterTM :: Key tm -> XT v -> tm v -> tm v
  lookupTM :: Key tm -> tm v -> Maybe v

  -- TODO: remove foldTM (redundant with Foldable tm) (also, current instances are backwards.)
  -- foldTM :: (a -> b -> b) -> tm a -> b -> b
  unionTM :: (v -> v -> v) -> tm v -> tm v -> tm v

  -- I almost certainly will need
  -- toList :: tm v -> [(Key tm, v)]
  -- More generally, foldWithKeyTM, I guess.

insertTM :: TrieMap tm => Key tm -> v -> tm v -> tm v
insertTM k v = alterTM k (\_ -> Just v)



-- | A 'BaseTrie' is a trie for a key type that has no internal structure.
newtype BaseTrie k v = BaseTrie (Map k v)

instance Traversable (BaseTrie k) where
  traverse f (BaseTrie m) = BaseTrie <$> traverse f m

instance Functor (BaseTrie k) where
  fmap f (BaseTrie m) = BaseTrie (fmap f m)

instance Foldable (BaseTrie k) where
  foldMap f (BaseTrie m) = foldMap f m

instance Ord k => TrieMap (BaseTrie k) where
  type Key (BaseTrie k) = k

  emptyTM = BaseTrie Map.empty
  lookupTM k (BaseTrie m) = Map.lookup k m
  alterTM k xt (BaseTrie m) = BaseTrie (Map.alter xt k m)
  -- foldTM f (BaseTrie m) z = Map.foldr f z m
  unionTM f (BaseTrie m1) (BaseTrie m2) = BaseTrie (Map.unionWith f m1 m2)


-- Enhance a trie by permitting empty and singleton tries.
data SEMap tm v
  = EmptySEM
  | SingleSEM (Key tm) v
  | MultiSEM (tm v)

instance Traversable tm => Traversable (SEMap tm) where
  traverse f EmptySEM = pure EmptySEM
  traverse f (SingleSEM k v) = SingleSEM k <$> f v
  traverse f (MultiSEM m) = MultiSEM <$> traverse f m

instance Functor tm => Functor (SEMap tm) where
  fmap f EmptySEM = EmptySEM
  fmap f (SingleSEM k v) = SingleSEM k (f v)
  fmap f (MultiSEM m) = MultiSEM (fmap f m)

instance Foldable tm => Foldable (SEMap tm) where
  foldMap f EmptySEM = mempty
  foldMap f (SingleSEM k v) = f v
  foldMap f (MultiSEM m) = foldMap f m

instance TrieMap tm => TrieMap (SEMap tm) where
  type Key (SEMap tm) = Key tm

  emptyTM = EmptySEM

  lookupTM k EmptySEM = Nothing
  lookupTM k (SingleSEM k' v) = case k == k' of
    True -> Just v
    False -> Nothing
  lookupTM k (MultiSEM m) = lookupTM k m

  alterTM k xt EmptySEM = case xt Nothing of
    Nothing -> EmptySEM
    Just v -> SingleSEM k v
  alterTM k xt (SingleSEM k' v) =
    if k == k' then
      case xt (Just v) of
        Nothing -> EmptySEM
        Just v' -> SingleSEM k' v'
    else
      case xt Nothing of
        Nothing -> SingleSEM k' v
        Just v' -> MultiSEM (insertTM k v' (insertTM k' v emptyTM))
  alterTM k xt (MultiSEM m) = MultiSEM (alterTM k xt m)

  unionTM f EmptySEM m2 = m2
  unionTM f m1 EmptySEM = m1
  unionTM f (SingleSEM k1 v1) (SingleSEM k2 v2) =
    MultiSEM (insertTM k2 v2 (insertTM k1 v1 emptyTM))
  unionTM f (SingleSEM k v) (MultiSEM m) =
    MultiSEM (alterTM k f' m)
    where
      f' Nothing = Just v
      f' (Just v') = Just (f v v')
  unionTM f (MultiSEM m) (SingleSEM k v) =
    MultiSEM (alterTM k f' m)
    where
      f' Nothing = Just v
      f' (Just v') = Just (f v' v)
  unionTM f (MultiSEM m1) (MultiSEM m2) = MultiSEM (unionTM f m1 m2)


data ListTrie tm v
  = ListTrie {
    listNil :: Maybe v
  , listCons :: tm (ListTrie tm v)
  }

instance Traversable tm => Traversable (ListTrie tm) where
  traverse f (ListTrie ln lc) = ListTrie <$> traverse f ln <*> traverse (traverse f) lc

instance Functor tm => Functor (ListTrie tm) where
  fmap f (ListTrie ln lc) = ListTrie (fmap f ln) (fmap (fmap f) lc)

instance Foldable tm => Foldable (ListTrie tm) where
  foldMap f (ListTrie ln lc) = foldMap f ln <> foldMap (foldMap f) lc

instance TrieMap tm => TrieMap (ListTrie tm) where
  type Key (ListTrie tm) = [Key tm]

  emptyTM = ListTrie { listNil = Nothing, listCons = emptyTM }

  lookupTM [] = listNil
  lookupTM (k:ks) = listCons >>> lookupTM k >=> lookupTM ks

  alterTM [] xt (ListTrie mn mc) = ListTrie (xt mn) mc
  alterTM (k:ks) xt (ListTrie mn mc) = ListTrie mn (alterTM k (liftXT (alterTM ks xt)) mc)

  unionTM f (ListTrie n1 c1) (ListTrie n2 c2) =
    ListTrie (unionMaybe f n1 n2) (unionTM (unionTM f) c1 c2)

-- Hmm. Perhaps I should have TrieMap instances for Maybe and for Map k v?
-- (that's what these basically are.)
-- type Key Maybe = ()
foldMaybe :: (v -> b -> b) -> Maybe v -> b -> b
foldMaybe f Nothing z = z
foldMaybe f (Just v) z = f v z

unionMaybe :: (v -> v -> v) -> Maybe v -> Maybe v -> Maybe v
unionMaybe f Nothing Nothing = Nothing
unionMaybe f (Just v) Nothing = Just v
unionMaybe f Nothing (Just v) = Just v
unionMaybe f (Just v1) (Just v2) = Just (f v1 v2)


liftXT :: TrieMap tm => (tm v -> tm v) -> XT (tm v)
liftXT f Nothing = Just (f emptyTM)
liftXT f (Just m) = Just (f m)



-- The basic idea of tries with binders is that the key is converted to a
-- locally-nameless representation "on the fly", sort of like how I do
-- alpha-equality, etc.
--
-- Instead of a single field for tyvar occurrences, there are now two fields:
-- bound tyvars and free tyvars.
--
-- Indexing into a trie with binding requires an auxiliary "bound variable
-- map", that maps tyvars to the level at which they are bound.
data SortTrie' v
  = SortTrie {
    sortInteger :: Maybe v
  , sortRecord :: RecordTrie v
  , sortClosure :: TeleTrie v
  , sortBoundVar :: BaseTrie BoundVar v
  , sortFreeVar :: BaseTrie TyVar v
  }

instance Traversable SortTrie' where
  traverse f (SortTrie mi mr mc mbv mfv) =
    SortTrie <$> traverse f mi <*> traverse f mr <*> traverse f mc <*> traverse f mbv <*> traverse f mfv

instance Functor SortTrie' where
  fmap f (SortTrie mi mr mc mbv mfv) =
    SortTrie (fmap f mi) (fmap f mr) (fmap f mc) (fmap f mbv) (fmap f mfv)

instance Foldable SortTrie' where
  foldMap f (SortTrie mi mr mc mbv mfv) =
    foldMap f mi <> foldMap f mr <> foldMap f mc <> foldMap f mbv <> foldMap f mfv

type SortTrie = SEMap SortTrie'

instance TrieMap SortTrie' where
  type Key SortTrie' = AKey Sort

  emptyTM = SortTrie Nothing emptyTM emptyTM emptyTM emptyTM

  lookupTM (AKey bvm (TyVarH aa)) = case lookupBVM aa bvm of
    Nothing -> sortFreeVar >>> lookupTM aa
    Just ix -> sortBoundVar >>> lookupTM ix
  lookupTM (AKey bvm IntegerH) = sortInteger
  lookupTM (AKey bvm (ClosureH tele)) = sortClosure >>> lookupTM (AKey bvm tele)

  alterTM (AKey bvm IntegerH) xt (SortTrie mi mr mc mbv mfv) =
    SortTrie (xt mi) mr mc mbv mfv
  alterTM (AKey bvm (TyVarH aa)) xt (SortTrie mi mr mc mbv mfv) =
    case lookupBVM aa bvm of
      Nothing -> SortTrie mi mr mc mbv (alterTM aa xt mfv)
      Just ix -> SortTrie mi mr mc (alterTM ix xt mbv) mfv
  alterTM (AKey bvm (ClosureH tele)) xt (SortTrie mi mr mc mbv mfv) =
    SortTrie mi mr (alterTM (AKey bvm tele) xt mc) mbv mfv
  alterTM (AKey bvm (RecordH rec)) xt (SortTrie mi mr mc mbv mfv) =
    SortTrie mi (alterTM (AKey bvm rec) xt mr) mc mbv mfv

  unionTM f (SortTrie i1 r1 c1 b1 f1) (SortTrie i2 r2 c2 b2 f2) =
    SortTrie (unionMaybe f i1 i2) (unionTM f r1 r2) (unionTM f c1 c2) (unionTM f b1 b2) (unionTM f f1 f2)


data TeleTrie' v
  = TeleTrie {
    teleEnd :: Maybe v
  , teleValue :: SortTrie (TeleTrie v)
  , teleType :: BaseTrie TyVar (TeleTrie v)
  }

instance Traversable TeleTrie' where
  traverse f (TeleTrie te tv tt) =
    TeleTrie <$> traverse f te <*> traverse (traverse f) tv <*> traverse (traverse f) tt

instance Functor TeleTrie' where
  fmap f (TeleTrie te tv tt) = TeleTrie (fmap f te) (fmap (fmap f) tv) (fmap (fmap f) tt)

instance Foldable TeleTrie' where
  foldMap f (TeleTrie te tv tt) = foldMap f te <> foldMap (foldMap f) tv <> foldMap (foldMap f) tt

type TeleTrie = SEMap TeleTrie'

instance TrieMap TeleTrie' where
  type Key TeleTrie' = AKey Tele

  emptyTM = TeleTrie Nothing emptyTM emptyTM

  lookupTM (AKey bvm TeleEnd) = teleEnd
  lookupTM (AKey bvm (ValueTele s tele)) =
    teleValue >>> lookupTM (AKey bvm s) >=> lookupTM (AKey bvm tele)
  lookupTM (AKey bvm (TypeTele aa tele)) =
    teleType >>> lookupTM aa >=> lookupTM (AKey bvm' tele)
    where bvm' = extendBVM aa bvm

  alterTM (AKey bvm TeleEnd) xt (TeleTrie te tv tt) = TeleTrie (xt te) tv tt
  alterTM (AKey bvm (ValueTele s t)) xt (TeleTrie te tv tt) =
    TeleTrie te (alterTM (AKey bvm s) (liftXT (alterTM (AKey bvm t) xt)) tv) tt
  alterTM (AKey bvm (TypeTele aa t)) xt (TeleTrie te tv tt) =
    TeleTrie te tv (alterTM aa (liftXT (alterTM (AKey bvm' t) xt)) tt)
    where bvm' = extendBVM aa bvm

  unionTM f (TeleTrie e1 v1 t1) (TeleTrie e2 v2 t2) =
    TeleTrie (unionMaybe f e1 e2) (unionTM (unionTM f) v1 v2) (unionTM (unionTM f) t1 t2)


data RecordTrie' v
  = RecordTrie {
    recEnd :: Maybe v
  , recExtend :: BaseTrie Label (SortTrie (RecordTrie v))
  }

instance Traversable RecordTrie' where
  traverse f (RecordTrie rn rc) = RecordTrie <$> traverse f rn <*> traverse (traverse (traverse f)) rc

instance Functor RecordTrie' where
  fmap f (RecordTrie rn rc) = RecordTrie (fmap f rn) (fmap (fmap (fmap f)) rc)

instance Foldable RecordTrie' where
  foldMap f (RecordTrie rn rc) = foldMap f rn <> foldMap (foldMap (foldMap f)) rc

type RecordTrie = SEMap RecordTrie'

instance TrieMap RecordTrie' where
  type Key RecordTrie' = AKey Record

  emptyTM = RecordTrie Nothing emptyTM

  lookupTM (AKey bvm RecEnd) = recEnd
  lookupTM (AKey bvm (RecExtend l s rec)) =
    recExtend >>> lookupTM l >=> lookupTM (AKey bvm s) >=> lookupTM (AKey bvm rec)

  alterTM (AKey bvm RecEnd) xt (RecordTrie rn rc) = RecordTrie (xt rn) rc
  alterTM (AKey bvm (RecExtend l s r)) xt (RecordTrie rn rc) =
    RecordTrie rn (alterTM l (liftXT (alterTM (AKey bvm s) (liftXT (alterTM (AKey bvm r) xt)))) rc)

  unionTM f (RecordTrie n1 c1) (RecordTrie n2 c2) =
    RecordTrie (unionMaybe f n1 n2) (unionTM (unionTM (unionTM f)) c1 c2)



-- 'bvmNext' is the current de Bruijn level.
data BoundVarMap = BVM { bvmLevel :: Int, bvmVars :: Map TyVar BoundVar }

newtype BoundVar = BoundVar Int
  deriving (Eq, Ord)

emptyBVM :: BoundVarMap
emptyBVM = BVM 0 Map.empty

lookupBVM :: TyVar -> BoundVarMap -> Maybe BoundVar
lookupBVM aa (BVM l m) = Map.lookup aa m

extendBVM :: TyVar -> BoundVarMap -> BoundVarMap
extendBVM aa (BVM l m) = BVM (l + 1) (Map.insert aa (BoundVar l) m)


-- Keys modulo alpha-equality
data AKey a = AKey BoundVarMap a

instance AEq a => Eq (AKey a) where
  AKey (BVM l1 m1) x1 == AKey (BVM l2 m2) x2 =
    l1 == l2 && aeq (AE l1 m1 m2) x1 x2

-- Alpha-equality
class AEq a where
  aeq :: AE -> a -> a -> Bool

data AE = AE { aeLevel :: Int, aeLhs :: Map TyVar BoundVar, aeRhs :: Map TyVar BoundVar }

lookupAE :: AE -> TyVar -> TyVar -> Bool
lookupAE (AE _ lhs rhs) aa bb = case (Map.lookup aa lhs, Map.lookup bb rhs) of
  (Nothing, Nothing) -> aa == bb
  (Just l1, Just l2) -> l1 == l2
  _ -> False

extendAE :: TyVar -> TyVar -> AE -> AE
extendAE aa bb (AE l lhs rhs) =
  AE (l+1) (Map.insert aa (BoundVar l) lhs) (Map.insert bb (BoundVar l) rhs)




-- demo: list of sorts, insert all into a trie. Show that trie deduplicates
-- (no dupes in this list, so just insert the list twice?)
--
-- Hmm. A problem. I think I also need to insert subterms.
-- This may be possible, by having (e.g.) Hoist collect (record|closure) sorts
-- recursively, but what about time complexity? I think it would be O(size^2).
-- (I don't really care about asymptotics? A normal map would need O(size * log
-- n * size), because O(log n) comparisons that each take O(size) time.
sorts :: [Sort]
sorts = [
    IntegerH
  , ClosureH (ValueTele IntegerH TeleEnd)
  , ClosureH (ValueTele IntegerH (ValueTele (ClosureH (ValueTele IntegerH TeleEnd)) TeleEnd))
  , ClosureH (TypeTele (TyVar "aa") (ValueTele (ClosureH (ValueTele (TyVarH (TyVar "aa")) TeleEnd)) TeleEnd))
  , RecordH RecEnd
  , RecordH (RecExtend (Label "l") IntegerH RecEnd)
  , RecordH (RecExtend (Label "l") IntegerH (RecExtend (Label "m") IntegerH RecEnd))
  , ClosureH (ValueTele (RecordH (RecExtend (Label "l") IntegerH RecEnd)) TeleEnd)
  ]

fromList :: TrieMap tm => [(Key tm, v)] -> tm v
fromList xs = foldr (\ (k, v) acc -> insertTM k v acc) emptyTM xs

-- Hmm. The tricky part of 'toList' is building the keys. (Particularly keys
-- with binders, because you need to generate fresh names)
--
-- I think you may be able to achieve this by using 'traverse' with a reader
-- monad:
-- 'local' to extend the current key, 'ask' at each value to extract the key.

main :: IO ()
main = do
  putStrLn "Hello, World!"
  let sorts' = sorts ++ sorts
  let trie = fromList $ map (\k -> (AKey emptyBVM k, k)) sorts' :: SortTrie Sort
  let trie' = flip evalState 0 $ traverse (\v -> do { i <- get; modify succ; pure (v, i) }) trie :: SortTrie (Sort, Int)
  print $ foldr (\_ i -> i+1) 0 trie
  print $ length sorts
  let values t = foldr (:) [] t
  mapM_ print (values trie)
  mapM_ print (values trie')

