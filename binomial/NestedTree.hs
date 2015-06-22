-- Functions for drawing binary trees as nested boxes
module NestedTree where

import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree

nestGap = 0.1
nestWidth = 1 - 1.5 * nestGap
nestHeight = 1 - 2 * nestGap
nestOff = (2 - nestGap)/4

-- Generate a 2x1 rectangle
drawNesting :: BTree () -> Diagram Cairo
drawNesting Empty = mempty
drawNesting (BNode _ l r) = mconcat
  [ drawNesting l # scaleToX nestWidth # scaleToY nestHeight # translateX (-nestOff)
  , drawNesting r # scaleToX nestWidth # scaleToY nestHeight # translateX nestOff
  , rect 2 1
  ]

t = BNode () (BNode () Empty Empty) (BNode () Empty Empty)
t2 = BNode () t t
t3 = BNode () t2 t2
t4 = BNode () t3 t3

main = defaultMain (drawNesting t4 # frame 0.5)
