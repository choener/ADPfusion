
module Main where

import Criterion.Main

import ADP.Fusion.GAPlike2



main = defaultMain
  [ bgroup "testTTT3"
    [ bench "  10" (whnf (testTTT 0)   10)
    , bench " 100" (whnf (testTTT 0)  100)
    , bench "1000" (whnf (testTTT 0) 1000)
    ]
  , bgroup "testTTTT4"
    [ bench "  10" (whnf (testTTTT 0)   10)
    , bench " 100" (whnf (testTTTT 0)  100)
    , bench "1000" (whnf (testTTTT 0) 1000)
    ]
  , bgroup "testTTTT4ga"
    [ bench "  10" (whnf (testTTTTga 0)   10)
    , bench " 100" (whnf (testTTTTga 0)  100)
    , bench "1000" (whnf (testTTTTga 0) 1000)
    ]
  ]
{-
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
-}
