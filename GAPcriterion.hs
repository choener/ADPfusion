
module Main where

import Criterion.Main

import ADP.Fusion.GAPlike



main = defaultMain
  [ bench "   1" (whnf (test2 0)    1)
  , bench "   5" (whnf (test2 0)    5)
  , bench "  10" (whnf (test2 0)   10)
  , bench "  15" (whnf (test2 0)   15)
  , bench "  20" (whnf (test2 0)   20)
  , bench "  50" (whnf (test2 0)   50)
  , bench " 100" (whnf (test2 0)  100)
  , bench " 250" (whnf (test2 0)  250)
  , bench " 500" (whnf (test2 0)  500)
  , bench "1000" (whnf (test2 0) 1000)
  ]
