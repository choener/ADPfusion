
{- Options_GHC -fno-liberate-case #-}
{- Options_GHC -fno-full-laziness #-}



module Main where

import Criterion.Main

import BenchmarkFun


main :: IO ()
main = return ()

{-
main :: IO ()
main = do
  defaultMain
    [ bgroup "Epsilon"
      [ bench "S"            $ nf stream_Epsilon_S 0
      , bench "V"            $ nf stream_Epsilon_V 0
      ]
    , bgroup "Chr"
      [ bench "S"            $ nf stream_Chr_S 1
      , bench "V"            $ nf stream_Chr_V 1
      ]
    , bgroup "Strng"
      [ bench "S"            $ nf stream_Strng_S  10
      , bench "V"            $ nf stream_Strng_V  10
      , bench "2S"           $ nf stream_Strng2_S 10
      , bench "2V"           $ nf (uncurry stream_Strng2_V) (10,0)
      ]
    ]
-}

