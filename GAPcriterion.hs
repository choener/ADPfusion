
module Main where

import ADP.Fusion.GAPlike2.Criterion



main = criterionMain

{-
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
-}

