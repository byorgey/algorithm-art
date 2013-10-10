{-# LANGUAGE NoMonomorphismRestriction #-}
module BWT where

import Diagrams.Prelude hiding (D)
import Diagrams.Backend.SVG.CmdLine
import Diagrams.Coordinates

import Test.QuickCheck

import Data.Char
import Data.List hiding (sort)
import Data.Maybe
import qualified Data.Map as M

import Data.Default.Class


-- Some parts from http://www.iis.sinica.edu.tw/~scm/pub/bwtJFP.pdf
bwt ws = (bwn, bwp)
  where
    bwp = map last . lexsort . rots $ ws
    bwn = succ . fromJust . findIndex (== ws) . lexsort . rots $ ws

rots xs = take (length xs) (iterate lrot xs)

lrot xs = tail xs ++ [head xs]

sortby f = sortBy (\x y -> if x `f` y then LT else GT)

lexsort ls = sortby (leq (length ls)) ls
  where
    leq 0  _      _     = True
    leq k (x:xs) (y:ys) = x < y || (x == y && leq (k-1) xs ys)

recreate :: Ord a => Int -> [a] -> [[a]]
recreate 0 ys = map (const []) ys
recreate k ys = sortby leq (join ys (recreate (k-1) ys))
  where leq us vs = head us <= head vs
        join xs xss = [y:ys | (y,ys) <- zip xs xss]

unbwt :: Ord a => Int -> [a] -> [a]
unbwt t ys = take (length ys) (thread (spl ys t))
  where thread (x,j) = x:thread (spl ys j)
        spl ys t = fromJust $ lookup t (zip [1..] (sortby (<=) (zip ys [1..])))

-----------

type D = Diagram SVG R2

alphabet :: Int -> D
alphabet i = c # lc (acolor i) # lw 0.05
  where
    l  = length cs
    cs = [red, orange, yellow, green, blue, purple]

    m  = abs i `mod` 10
    c  = mconcat [circle (fromIntegral (m + 1 - r) / fromIntegral (m + 1)) | r <- [0..m]]

acolor :: Int -> Colour Double
acolor i = cs !! (abs i `mod` l)
  where
    l  = length cs
    cs = [red, orange, yellow, green, blue, purple]

d :: D
d = hcat' def { sep = 0.1 } $ map centerXY
    [ reflectX $ block rs  -- Rotations of s
    , sorting
    , block rs' -- sorted rotations of s
    ]
  where
    row = hcat' def { sep = 0.1 }
    block = vcat' def { sep = 0.1 } . map (row . map alphabet)

    sorting = reflectY $ mconcat 
            [ connect i j # lc (acolor $ head r)
            | (i,r) <- zip [0..] rs
            , let j = fromJust . findIndex (== r) $ rs'
            ]
--    connect i j = (0 & f i) ~~ (5 & f j) # lw 0.2
    connect i j = bez (0 & f i) (2 & f i) (3 & f j) (5 & f j) # lw 0.05
      where
        f x = fromIntegral x * 2.1

    rs  = rots s
    rs' = lexsort rs

    s = map ((subtract (ord '0')) . ord) "101103107109113" -- This should be something more meaningful

bez a b c d = trailLike $ (fromSegments [bezier3 (b .-. a) (c .-. a) (d .-. a)]) `at` a

d' :: D
d' = hcat' def { sep = 0.1 } (map alphabet [0..10])

main = defaultMain (d # centerXY # pad 1.1)

-----------------------------------

prop_unbwt_bwt :: String -> Bool
prop_unbwt_bwt xs = xs == (uncurry unbwt . bwt $ xs)