{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving        #-}
module Binomial where

import           Diagrams.Backend.SVG.CmdLine
import           Diagrams.Prelude             hiding (D)

import           Data.List                    (find)
import           Data.Tree                    (Tree (..))

-- Taken from Louis Wasserman, "Playing with Priority Queues",
-- Monad.Reader Issue 16.

{- A binomial tree of rank k is defined inductively as follows:

   * A binomial tree of rank 0 is a node with no children.

   * A binomial tree of rank k+1 is a node with one child of each rank
     i, 0 <= i <= k.

A *binomial forest* is a list of binomial trees, with at most one of
each rank. We will assume that the trees are in ascending order of
rank. A *binomial heap* is a binomial forest in which every tree
satisfies the heap property.

A binomial tree of rank k has size 2^k. Thus, if a binomial forest has
total size n, then it has a tree of rank k iff n has a 1 in the kth
bit of its binary representation. Note that this implies that the
number of trees in a binomial forest is at most log n + 1.
-}

class Eq1 f where
  eq1 :: Eq a => f a -> f a -> Bool

-- Zero a is like the empty list.
data Zero a = Zero
  deriving Eq

instance Eq1 Zero where
  eq1 Zero Zero = True

-- Succ rank a  is list of binomial trees of ranks [rank, rank-1, ... 0]
data Succ rank a = BinomTree rank a :<: rank a

instance Eq1 rank => Eq1 (Succ rank) where
  eq1 (t1 :<: ts1) (t2 :<: ts2) = (t1 == t2) && (eq1 ts1 ts2)

-- A binomial tree of rank n has a value at the root and a list of
-- n children of ranks [n-1, ... 0].
data BinomTree rank a = BinomTree a (rank a)

instance (Eq a, Eq1 rank) => Eq (BinomTree rank a) where
  (BinomTree a1 ts1) == (BinomTree a2 ts2) = (a1 == a2) && (eq1 ts1 ts2)

-- Binomial forests are like binary numbers.  The rank is the *least
-- significant* bit.
data BinomForest rank a
  = Nil
  | O (BinomForest (Succ rank) a)
  | I (BinomTree rank a) (BinomForest (Succ rank) a)

instance (Eq1 rank, Eq a) => Eq (BinomForest rank a) where
  Nil == Nil = True
  (O f1) == (O f2) = f1 == f2
  (I t1 f1) == (I t2 f2) = (t1 == t2) && (f1 == f2)

type BinomHeap = BinomForest Zero

-- Merge two trees into one.  2^k + 2^k = 2^(k+1).
-- Preserve the heap property.
(/\) :: Ord a => BinomTree rank a -> BinomTree rank a -> BinomTree (Succ rank) a
t1@(BinomTree x1 ts1) /\ t2@(BinomTree x2 ts2)
  | x1 <= x2  = BinomTree x1 (t2 :<: ts1)
  | otherwise = BinomTree x2 (t1 :<: ts2)

-- Merge two binomial forests.  Analogous to binary addition.

mergeForest :: Ord a => BinomForest rank a -> BinomForest rank a -> BinomForest rank a
mergeForest ts1 ts2 = case (ts1, ts2) of
  (Nil, _  ) -> ts2
  (_  , Nil) -> ts1
  (O ts1', O ts2')       -> O (mergeForest ts1' ts2')
  (O ts1', I t2 ts2')    -> I t2 (mergeForest ts1' ts2')
  (I t1 ts1', O ts2')    -> I t1 (mergeForest ts1' ts2')
  (I t1 ts1', I t2 ts2') -> O (carryForest (t1 /\ t2) ts1' ts2')

carryForest
  :: Ord a
  => BinomTree rank a -> BinomForest rank a -> BinomForest rank a
  -> BinomForest rank a
carryForest t0 ts1 ts2 = case (ts1, ts2) of
  (Nil, _)    -> incrForest t0 ts2
  (_, Nil)    -> incrForest t0 ts1
  (O ts1', _) -> mergeForest (I t0 ts1') ts2
  (_, O ts2') -> mergeForest ts1 (I t0 ts2')
  (I t1 ts1', I t2 ts2') -> I t0 (carryForest (t1 /\ t2) ts1' ts2')

incrForest :: Ord a => BinomTree rank a -> BinomForest rank a -> BinomForest rank a
incrForest t Nil        = I t Nil
incrForest t (O ts')    = I t ts'
incrForest t (I t' ts') = O (incrForest (t /\ t') ts')

insert :: Ord a => a -> BinomHeap a -> BinomHeap a
insert a h = incrForest (BinomTree a Zero) h

------------------------------------------------------------

-- Dissected variant of binomial forest merge, for visualizing the
-- process

-- | Are we going down the call tree (with some inputs) or up (with an
--   output)?
data Call rank a
  = CallMerge (BinomForest rank a) (BinomForest rank a)
  | CallCarry (BinomTree rank a) (BinomForest rank a) (BinomForest rank a)
  | Result (BinomForest rank a)
  deriving (Eq)

data CallStack rank a where
  Top    :: CallStack Zero a
  MergeO :: CallStack rank a -> CallStack (Succ rank) a
  MergeI :: BinomTree rank a -> CallStack rank a -> CallStack (Succ rank) a
  MergeOCarry :: CallStack rank a -> CallStack (Succ rank) a
  CarryMerge :: CallStack rank a -> CallStack rank a
  CarryCarry :: BinomTree rank a -> CallStack rank a -> CallStack (Succ rank) a

data MergeState a where
  MS :: Call rank a
     -> CallStack rank a
     -> MergeState a

mergeForest' :: Ord a => MergeState a -> MergeState a
mergeForest' (MS (CallMerge Nil ts2) stk) = MS (Result ts2) stk
mergeForest' (MS (CallMerge ts1 Nil) stk) = MS (Result ts1) stk
mergeForest' (MS (CallMerge (O ts1') (O ts2')) stk)
  = MS (CallMerge ts1' ts2') (MergeO stk)
mergeForest' (MS (CallMerge (O ts1') (I t2 ts2')) stk)
  = MS (CallMerge ts1' ts2') (MergeI t2 stk)
mergeForest' (MS (CallMerge (I t1 ts1') (O ts2')) stk)
  = MS (CallMerge ts1' ts2') (MergeI t1 stk)
mergeForest' (MS (CallMerge (I t1 ts1') (I t2 ts2')) stk)
  = MS (CallCarry (t1 /\ t2) ts1' ts2') (MergeOCarry stk)
mergeForest' (MS (CallCarry t0 Nil ts2) stk)
  = MS (Result (incrForest t0 ts2)) stk
mergeForest' (MS (CallCarry t0 ts1 Nil) stk)
  = MS (Result (incrForest t0 ts1)) stk
mergeForest' (MS (CallCarry t0 (O ts1') ts2) stk)
  = MS (CallMerge (I t0 ts1') ts2) (CarryMerge stk)
mergeForest' (MS (CallCarry t0 ts1 (O ts2')) stk)
  = MS (CallMerge ts1 (I t0 ts2')) (CarryMerge stk)
mergeForest' (MS (CallCarry t0 (I t1 ts1') (I t2 ts2')) stk)
  = MS (CallCarry (t1 /\ t2) ts1' ts2') (CarryCarry t0 stk)

mergeForest' (MS (Result f) (MergeO stk)) = MS (Result (O f)) stk
mergeForest' (MS (Result f) (MergeI t stk)) = MS (Result (I t f)) stk
mergeForest' (MS (Result f) (MergeOCarry stk)) = MS (Result (O f)) stk
mergeForest' (MS (Result f) (CarryMerge stk)) = MS (Result f) stk
mergeForest' (MS (Result f) (CarryCarry t stk)) = MS (Result (I t f)) stk

prop_mergeForest_dissected :: Ord a => BinomHeap a -> BinomHeap a -> Bool
prop_mergeForest_dissected f1 f2 =
  Just (mergeForest f1 f2) ==
    (extract <$> find mergeDone (iterate mergeForest' (MS (CallMerge f1 f2) Top)))
  where
    mergeDone (MS (Result _) Top) = True
    mergeDone _                   = False
    extract (MS (Result f) Top)   = f
    extract _                     = error "DON'T PANIC"

------------------------------------------------------------

type D = Diagram SVG R2

class RankToForest r where
  rankToForest :: r a -> [Tree a]

toTree :: RankToForest rank => BinomTree rank a -> Tree a
toTree (BinomTree a ts) = Node a (rankToForest ts)

instance RankToForest Zero where
  rankToForest Zero = []

instance RankToForest rank => RankToForest (Succ rank) where
  rankToForest (t :<: ts) = toTree t : rankToForest ts

toForest :: RankToForest rank => BinomForest rank a -> [Maybe (Tree a)]
toForest Nil     = []
toForest (O f)   = Nothing : toForest f
toForest (I t f) = Just (toTree t) : toForest f

drawNode :: Int -> D
drawNode n = circle (fromIntegral n * 0.1 + 1) # fc blue

drawTree :: Tree Int -> D
drawTree (Node n ts)
    = vcat' with {sep = treeSize}
    [ drawNode n # setEnvelope mempty
    , children
    ]
    # withNameAll () (beneath . mconcat . map ((origin ~~) . location))
    # localize
  where
    children
      = ts
      # map (named () . drawTree)
      # reverse
      # cat' unit_X with {sep = treeSize}

-- drawTree t
--   = renderTree (const (circle 1 # fc black))
--                (~~)
--                (symmLayout' with { slHSep = treeSize, slVSep = treeSize } t)
--    # lw 0.03
--    # centerX
--    <> strutX (treeSize * 2)

treeSize :: Num a => a
treeSize = 4

drawForest :: [Maybe (Tree Int)] -> D
drawForest
  = alignR
  . hcat
  . reverse
  . map (\(w, t) -> maybe mempty (centerX . drawTree) t <> strutX (w * treeSize))
  . zip (1 : iterate (*2) 1)

drawMergeState :: MergeState a -> D
drawMergeState (MS (CallMerge f1 f2) stk) = undefined  -- XXX todo

heaps :: [BinomHeap Int]
heaps = scanr insert Nil [1,3,5,4,4,5,2,3,1,3,3,2,2,3,1,4,5,2,3,4,1,5,1,3,1,2,2,4,4,2,3,4,5,2,2,5,5,4,1,1,1,1,1,1]

dia :: D
dia
  = vcat' with {sep = treeSize}
  . map (drawForest . toForest)
  $ heaps

main :: IO ()
main = defaultMain (dia # centerXY # sized (Width 4) # pad 1.1)

-- to do:
--   * use Char data in heaps and show with color
--   * visualize mergeForest operation
