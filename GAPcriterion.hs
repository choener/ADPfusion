
module Main where

import Criterion.Main

import ADP.Fusion.GAPlike2



main = defaultMain
  [ bgroup "three tables, O(n^2)"
    [ bench "   10" (whnf (testM3 0)    10)
    , bench "  100" (whnf (testM3 0)   100)
    , bench " 1000" (whnf (testM3 0)  1000)
    ]
  , bgroup "four tables, O(n^3)"
    [ bench "   10" (whnf (testM4 0)    10)
    , bench "  100" (whnf (testM4 0)   100)
    , bench " 1000" (whnf (testM4 0)  1000)
    ]
  ]

