{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Binomial where

import           Diagrams.Backend.SVG.CmdLine
import           Diagrams.Coordinates
import           Diagrams.Prelude             hiding (D)

import           Data.Tree                    (Tree (..))
import           Diagrams.TwoD.Layout.Tree

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

-- Zero a is like the empty list.
data Zero a = Zero

-- Succ rank a  is list of binomial trees of ranks [rank, rank-1, ... 0]
data Succ rank a = BinomTree rank a :<: rank a

-- A binomial tree of rank n has a value at the root and a list of
-- n children of ranks [n-1, ... 0].
data BinomTree rank a = BinomTree a (rank a)

-- Binomial forests are like binary numbers.  The rank is the *least
-- significant* bit.
data BinomForest rank a
  = Nil
  | O (BinomForest (Succ rank) a)
  | I (BinomTree rank a) (BinomForest (Succ rank) a)

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
  (O ts1', O ts2')    -> O (mergeForest ts1' ts2')
  (O ts1', I t2 ts2') -> I t2 (mergeForest ts1' ts2')
  (I t1 ts1', O ts2') -> I t1 (mergeForest ts1' ts2')
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
drawNode n
  = iterate (+0.3) 0.5
  # take n
  # map circle
  # mconcat

drawTree :: Tree Int -> D
drawTree (Node n ts)
    = vcat' with {sep = treeSize}
    [ drawNode n # setEnvelope mempty
    , children
    ]
    # withNameAll () (atop . mconcat . map ((origin ~~) . location))
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

treeSize = 4

drawForest
  = alignR
  . hcat
  . reverse
  . map (\(w, t) -> maybe mempty (centerX . drawTree) t <> strutX (w * treeSize))
  . zip (1 : iterate (*2) 1)

trees = scanr insert Nil [1,3,5,4,4,5,2,3,1,3,3,2,2,3,1,4,5,2,3,4,1,5]

dia
  = vcat' with {sep = treeSize}
  . map (drawForest . toForest)
  $ trees

main = defaultMain (dia # centerXY # sized (Width 4) # pad 1.1)

-- to do:
--   * draw binomial trees in right-leaning style?
--   * use Char data in trees and show with color
--   * visualize mergeForest operation
