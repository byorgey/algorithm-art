{-# LANGUAGE NoMonomorphismRestriction #-}
module BWT where

import Diagrams.Prelude
import Diagrams.Backend.SVG.CmdLine
import Diagrams.Coordinates

import Test.QuickCheck hiding ((===))

import Data.Char
import Data.List hiding (sort)
import Data.Maybe
import qualified Data.Map as M

import Data.Default.Class

import Debug.Trace


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

alphabet' :: Int -> Diagram B
alphabet' i = c # lc (acolor i) # lwG 0.05 # withEnvelope (circle 1 :: Diagram B)
  where
    l  = length cs
    cs = [red, orange, yellow, green, blue, purple]

    m  = abs i `mod` 2
    c  = mconcat [circle (fromIntegral (m + 1 - r) / fromIntegral (m + 1) * (1 + 1/6 - (fromIntegral ((i `mod` 10) `div` 2) + 1) / 6)) | r <- [0..m]]

alphabet :: Int -> Diagram B
alphabet (-1) = square 1 # lc red # lwG 0.05 # withEnvelope (circle 1 :: Diagram B)
alphabet i    = c # lc (acolor i) # lwG 0.05
  where
    l  = length cs
    cs = [red, orange, yellow, green, blue, purple]

    m  = abs i `mod` 10
    c  = mconcat [circle (fromIntegral (m + 1 - r) / fromIntegral (m + 1)) | r <- [0..m]]

acolor :: Int -> Colour Double
acolor (-1) = red
acolor i = cs !! (abs i `mod` l)
  where
    l  = length cs
    cs = [red, orange, yellow, green, blue, purple]

d :: Diagram B
d = squared -- horizontal 
  where
    vsep = 0.1 
    hsep = 0.1

{-    sweeping = (sweepLayout (1/2 @@ turn) $ map centerXY
     [ block rs
     , sorting 7 head rs rs'
     , block rs'
     , bwtToRLE
     , reflectX bwtToRLE
     , reflectX $ block [[a,b] | (a,b) <- zip p [1..]]
     , sorting 7 fst (zip p [1..]) (sortby (<=) (zip p [1..]))
     , block [[a,b,i] | (i,(a,b)) <- zip [1..] $ sortby (<=) (zip p [1..])]
     ]) === centerXY (threads n p)
 -}
    horizontal = hcat' (with & sep .~ 1) $ map centerXY 
     [ inputToBWT
     , bwtToRLE
     , reflectX bwtToRLE
     , bwtToInput
     ]

    squared = vcat' (with & sep .~ 2) [ alignL top, translate ((-2) ^& 0) $ alignL bottom ]
      where
        top    = reflectY $ f [ inputToBWT, bwtToRLE ]
        bottom = rotate (1/2 @@ turn) $ reflectY $ f
          [ reflectX bwtToRLE
          , bwtToInput
          ]
        f ds = hcat' (with & sep .~ 2) (map centerXY ds)

    inputToBWT = hcat' (with & sep .~ hsep) $ map centerXY
      [ reflectX $ block rs  -- Rotations of s
      , sorting 7 head rs rs'
      , block rs' -- sorted rotations of s
      ]

    buildUnbwt = hcat' (with & sep .~ hsep) $ map centerXY
     [ reflectX $ block [[a,b] | (a,b) <- zip p [1..]]           -- spl table
     , sorting 23.1 fst (zip p [1..]) (sortby (<=) (zip p [1..]))
     , block [[a,b,i] | (i,(a,b)) <- zip [1..] $ sortby (<=) (zip p [1..])] -- continued
     ]
    bwtToInput = hcat' (with & sep .~ 7) $ map alignB [ buildUnbwt, threads n p ]

    bwtToRLE = vcat' (with & sep .~ vsep) $ map (hcat' (with & sep .~ hsep) . map alphabet) $ groupBy (==) p

    tw = -2
    threads n p =   alignL (hcat' (with & sep .~ tw+2+hsep) (map (alphabet . snd) is)) 
                === alignL ((reflectY $ hcat' (with & sep .~ tw) $ take (length p * 2 - 1) ds))
      where
        (is,ds) = mconcat [ ([(i,x)],
                              [ moveTo (0 ^& (fromIntegral i * (2+vsep))) (centerXY (block [[x,j]]))
--                              , connect tw i j
                              ])
                     | (i,x,j) <- ts
                     ]
        ts = take (length p) (thread n (spl n))
        thread i (x,j) = (i,x,j) : thread j (spl j)
        spl t = fromJust $ lookup t (zip [1..] (sortby (<=) (zip p [1..])))

    

    row = hcat' (with & sep .~ hsep)
    block = vcat' (with & sep .~ vsep) . map (row . map alphabet)

    sorting w f rs rs' = reflectY $ mconcat 
            [ connect w i j # lc (acolor (f r))
            | (i,r) <- zip [0..] rs
            , let j = fromJust . findIndex (== r) $ rs'
            ]
--    connect i j = (0 ^& f i) ~~ (5 ^& f j) # lwG 0.2
    connect w i j = bez (0 ^& f i) (w*2/5 ^& f i) (w*3/5 ^& f j) (w ^& f j) # lwG 0.05
      where
        f x = fromIntegral x * (2+vsep)

    rs  = rots s
    rs' = lexsort rs

    s = (-1) : map ((subtract (ord '0')) . ord) "101103107109113" -- This should be something more meaningful
    (n,p) = bwt s

{-
sweepLayout sweep ds = mconcat $ zipWith f ds (scanl (+) 0 ts)
  where
    f d t = d # rotate (1/4 @@ turn) # alignL # moveTo (r ^& 0) # rotate t

    r = total / (tau * getTurn sweep)
    l = fromIntegral $ length ds
    bbs = map boundingBox ds
    ws' = map (fst . unr2 . boxExtents) bbs
    wh = head ws'
    wl = last ws'
    ws = (wh / 2) : ((zipWith ave<*>tail) (drop 1 . take (length ds - 2) $ ws')) ++ [wl / 2]
    ave a b = (a + b) / 2
    total = sum ws
    ts = map ((/(total @@ turn)) . (*sweep) . Turn) ws
-}
bez a b c d = trailLike $ (fromSegments [bezier3 (b .-. a) (c .-. a) (d .-. a)]) `at` a

d' :: Diagram B
d' = vcat' (with & sep .~ 0.1) (map alphabet [0..10])

main = defaultMain (d # centerXY # pad 1.1)
-- main = defaultMain (sweepLayout (Turn 1/2) (map square [1,2,4,3,2,3,2,1,2]) # centerXY # pad 1.1)

-----------------------------------

prop_unbwt_bwt :: String -> Bool
prop_unbwt_bwt xs = xs == (uncurry unbwt . bwt $ xs)
