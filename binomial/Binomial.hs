{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving        #-}
module Binomial where

import           Diagrams.Backend.SVG.CmdLine
import           Diagrams.Prelude             hiding (D)

import           Data.Char                    (ord)
import           Data.List                    (find, transpose)
import           Data.Tree                    (Tree (..))

class Drawable a where
  draw :: a -> D

instance Drawable Int where
  draw n = circle (fromIntegral n * 0.1 + 1) # fc blue

instance Drawable Char where
  draw x = circle 1 # fc c
    where c = clist !! (ord x `mod` (length clist))
          clist = [red, orange, yellow, green, blue, purple, white]

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
  (Nil, _)               -> incrForest t0 ts2
  (_, Nil)               -> incrForest t0 ts1
  (O ts1', O ts2')       -> I t0 (mergeForest ts1' ts2')
  (O ts1', I t2 ts2')    -> O (carryForest (t0 /\ t2) ts1' ts2')
  (I t1 ts1', O ts2')    -> O (carryForest (t1 /\ t0) ts1' ts2')
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

-- | The current function call.
data Call rank a
  = CallMerge (BinomForest rank a) (BinomForest rank a)  -- calling mergeForest
  | CallCarry (BinomTree rank a) (BinomForest rank a) (BinomForest rank a)
                                                         -- calling carryForest
  | Result (BinomForest rank a)                          -- returning up the tree with a result
  deriving (Eq)

-- | The current \"call stack\", i.e. what we need to compute while
-- unwinding the recursion.
data CallStack rank a where
  Top  :: CallStack Zero a  -- top of the stack.
  AddO :: RankToForest rank
       => Maybe (BinomTree rank a)   -- trees that were added, resulting in 0 bit
       -> Maybe (BinomTree rank a)
       -> CallStack rank a           -- rest of the call stack
       -> CallStack (Succ rank) a
  AddI :: RankToForest rank
       => Maybe (BinomTree rank a)   -- trees that were added...
       -> Maybe (BinomTree rank a)
       -> BinomTree rank a           -- resulting in this tree
       -> CallStack rank a           -- rest of the call stack
       -> CallStack (Succ rank) a

-- | A frozen snapshot of some intermediate state in the merge
--   algorithm, with a current function call and a call stack.
data MergeState a where
  MS :: RankToForest rank
     => Call rank a
     -> CallStack rank a
     -> MergeState a

-- | Perform one small step from a MergeState to the next.
mergeForest' :: Ord a => MergeState a -> MergeState a
mergeForest' (MS (CallMerge Nil ts2) stk) = MS (Result ts2) stk
mergeForest' (MS (CallMerge ts1 Nil) stk) = MS (Result ts1) stk
mergeForest' (MS (CallMerge (O ts1') (O ts2')) stk)
  = MS (CallMerge ts1' ts2') (AddO Nothing Nothing stk)
mergeForest' (MS (CallMerge (O ts1') (I t2 ts2')) stk)
  = MS (CallMerge ts1' ts2') (AddI Nothing (Just t2) t2 stk)
mergeForest' (MS (CallMerge (I t1 ts1') (O ts2')) stk)
  = MS (CallMerge ts1' ts2') (AddI (Just t1) Nothing t1 stk)
mergeForest' (MS (CallMerge (I t1 ts1') (I t2 ts2')) stk)
  = MS (CallCarry (t1 /\ t2) ts1' ts2') (AddO (Just t1) (Just t2) stk)
mergeForest' (MS (CallCarry t0 Nil ts2) stk)
  = MS (Result (incrForest t0 ts2)) stk
mergeForest' (MS (CallCarry t0 ts1 Nil) stk)
  = MS (Result (incrForest t0 ts1)) stk
mergeForest' (MS (CallCarry t0 (O ts1') (O ts2')) stk)
  = MS (CallMerge ts1' ts2') (AddI Nothing Nothing t0 stk)
mergeForest' (MS (CallCarry t0 (O ts1') (I t2 ts2')) stk)
  = MS (CallCarry (t0 /\ t2) ts1' ts2') (AddO Nothing (Just t2) stk)
mergeForest' (MS (CallCarry t0 (I t1 ts1') (O ts2')) stk)
  = MS (CallCarry (t1 /\ t0) ts1' ts2') (AddO (Just t1) Nothing stk)
mergeForest' (MS (CallCarry t0 (I t1 ts1') (I t2 ts2')) stk)
  = MS (CallCarry (t1 /\ t2) ts1' ts2') (AddI (Just t1) (Just t2) t0 stk)

mergeForest' (MS (Result f) (AddO _ _ stk)) = MS (Result (O f)) stk
mergeForest' (MS (Result f) (AddI _ _ t stk)) = MS (Result (I t f)) stk

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

drawTree :: Drawable a => Tree a -> D
drawTree (Node a ts)
    = vcat' with {sep = treeSize}
    [ draw a # setEnvelope mempty
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

drawBTree :: (Drawable a, RankToForest rank) => BinomTree rank a -> D
drawBTree = drawTree . toTree

-- drawTree t
--   = renderTree (const (circle 1 # fc black))
--                (~~)
--                (symmLayout' with { slHSep = treeSize, slVSep = treeSize } t)
--    # lw 0.03
--    # centerX
--    <> strutX (treeSize * 2)

treeSize :: Num a => a
treeSize = 4

drawForest :: Drawable a => [Maybe (Tree a)] -> D
drawForest
  = alignR
  . hcat
  . reverse
  . map (\(w, t) -> maybe mempty (centerX . drawTree) t <> strutX (w * treeSize))
  . zip (1 : iterate (*2) 1)

data MBit = Blank | BitO | BitI D

maybeToBit :: MBit -> Maybe D -> MBit
maybeToBit m Nothing  = m
maybeToBit _ (Just d) = BitI d

bitToMaybe :: MBit -> Maybe D
bitToMaybe Blank    = Nothing
bitToMaybe BitO     = Nothing
bitToMaybe (BitI d) = Just d

withB, withO :: Maybe D -> MBit
withB = maybeToBit Blank
withO = maybeToBit BitO

drawBit :: MBit -> D
drawBit Blank    = mempty
drawBit BitO     = square 1 # fc black
drawBit (BitI d) = d

type Addition = [Column]
type Column = [MBit]

layoutMergeState :: Drawable a => MergeState a -> Addition
layoutMergeState (MS call stk) =
    layoutCall call ++ layoutStack stk

layoutCall :: (Drawable a, RankToForest rank) => Call rank a -> Addition
layoutCall (CallMerge   f1 f2) = reverse $ layoutForests Nothing f1 f2
layoutCall (CallCarry t f1 f2) = reverse $ layoutForests (Just t) f1 f2
layoutCall (Result f)          = toResult . reverse $ layoutForests Nothing f Nil
  where
    toResult = map (\[c,f1,f2,r] -> [c,r,f2,f1])

layoutForests :: (Drawable a, RankToForest rank) => Maybe (BinomTree rank a) -> BinomForest rank a -> BinomForest rank a -> Addition
layoutForests Nothing Nil Nil = []
layoutForests carry Nil Nil
  = [ [ Blank
      , Blank
      , Blank
      , withB $ drawBTree <$> carry
    ] ]
layoutForests carry f1 f2
  = [ withB $ drawBTree <$> carry
    , withO $ drawBTree <$> t1
    , withO $ drawBTree <$> t2
    , Blank
    ]
    :
    layoutForests Nothing f1' f2'
  where (t1, f1') = splitForest f1
        (t2, f2') = splitForest f2

splitForest :: BinomForest t a -> (Maybe (BinomTree t a), BinomForest (Succ t) a)
splitForest Nil     = (Nothing , Nil)
splitForest (O f)   = (Nothing , f)
splitForest (I t f) = (Just t  , f)

layoutStack :: (Drawable a, RankToForest rank) => CallStack rank a -> Addition
layoutStack Top = []
layoutStack (AddO t1 t2 stk)
  = [ Blank
    , withO $ drawBTree <$> t1
    , withO $ drawBTree <$> t2
    , BitO
    ]
    : layoutStack stk
layoutStack (AddI t1 t2 r stk)
  = [ Blank
    , withO $ drawBTree <$> t1
    , withO $ drawBTree <$> t2
    , BitI $ drawBTree r
    ]
    : layoutStack stk

-- blergh, need some grid layout stuff in -lib already!
drawAddition :: Addition -> D
drawAddition grid = grid'
  where
    grid1   = grid
            # map (map (centerX . drawBit))
            # map (zipWith scale (0.5 : repeat 1))
    grid'   = grid1
            # reverse
            # zipWith (\w -> map (strutX w <>)) (treeSize : iterate (*2) treeSize)
            # reverse
            # map (zipWith (\h -> (strutY h # alignT <>)) heights)
            # transpose
            # map (alignR . hcat' with {sep = treeSize})
            # (\rows@[carries, add1, add2, res] ->
                 vcat' with {sep = treeSize}
                   [carries, add1, add2, hrule (maximum . map width $ rows) # alignR, res]
              )
    heights = foldl1 (zipWith max) (map (map height) grid1)

drawMergeState :: Drawable a => MergeState a -> D
drawMergeState = drawAddition . layoutMergeState

heaps1 :: [BinomHeap Char]
heaps1 = scanl (flip insert) Nil "Hello there, this is a visualization of a binomial forest merge operation, which is a more elaborate version of binary addition."

heaps2 :: [BinomHeap Char]
heaps2 = scanl (flip insert) Nil "Twinkle, twinkle, little star, how I wonder what you are."

dia :: D
dia
  = vcat' with {sep = treeSize}
  . map (drawForest . toForest)
  $ heaps1

visualizeMerge :: (Ord a, Drawable a) => BinomHeap a -> BinomHeap a -> D
visualizeMerge h1 h2
    = vcat
    . map (enbox grey treeSize . drawMergeState)
    . takeUntil isResult
    $ steps
  where
    steps = iterate mergeForest' (MS (CallMerge h1 h2) Top)
    isResult (MS (Result _) _) = True
    isResult _ = False
    takeUntil _ [] = []
    takeUntil p (x:xs)
      | p x = [x]
      | otherwise = x : takeUntil p xs

enbox :: Colour Double -> Double -> D -> D
enbox c padding d = centerXY d <> rect (width d + 2*padding) (height d + 2*padding) # lc c

main :: IO ()
main = defaultMain (visualizeMerge (heaps1 !! 38) (heaps2 !! 19) # centerXY # sized (Width 4) # pad 1.1)

