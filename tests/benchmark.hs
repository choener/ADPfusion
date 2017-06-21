
{- Options_GHC -fno-liberate-case #-}
{- Options_GHC -fno-full-laziness #-}



module Main where

import Criterion.Main
import Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Util
import Data.Vector.Unboxed as VU
import Debug.Trace
import Data.Char (ord)

import ADP.Fusion.Point
import Data.PrimitiveArray hiding (map, unsafeIndex)



-- ** Epsilon

stream_Epsilon_S :: Int -> Int
stream_Epsilon_S k = unId $ (f <<< Epsilon ... h) (pointLI 10) (pointLI k)
  where f _ = 100099 :: Int
        h   = S.foldl' max 100011
{-# NoInline stream_Epsilon_S #-}

stream_Epsilon_V :: Int -> Int
stream_Epsilon_V k = unId $ (f <<< (M:|Epsilon:|Epsilon) ... h) (Z:.pointLI 10:.pointLI 10) (Z:.pointLI k:.pointLI k)
  where f _ = 100099 :: Int
        h   = S.foldl' max 100011
{-# NoInline stream_Epsilon_V #-}


-- ** Char

v1 = VU.fromList "ACGUACGUACGU1"
v2 = VU.fromList "ACGUACGUACGU2"
v3 = VU.fromList "ACGUACGUACGU3"
v4 = VU.fromList "ACGUACGUACGU4"

stream_Chr_S :: Int -> Int
stream_Chr_S k = seq v1 $ unId $ (f <<< chr v1 ... h) (pointLI 10) (pointLI k)
  where f p = ord p + 100099 :: Int
        h   = S.foldl' max 100011
{-# NoInline stream_Chr_S #-}

stream_Chr_V :: Int -> Int
stream_Chr_V k = seq v1 $ seq v2 $ unId $ (f <<< (M:|chr v1:|chr v2) ... h) (Z:.pointLI 10:.pointLI 10) (Z:.pointLI k:.pointLI k)
  where f (Z:.p:.q) = ord p + ord q + 100099 :: Int
        h           = S.foldl' max 100011
{-# NoInline stream_Chr_V #-}

-- **

stream_Strng_S :: Int -> Int
stream_Strng_S k = seq v1 $ unId $ (f <<< Strng v1 ... h) (pointLI 10) (pointLI k)
  where f zs = VU.sum (VU.map ord zs)
        h   = S.foldl' (+) 0
{-# NoInline stream_Strng_S #-}

stream_Strng_V :: Int -> Int
stream_Strng_V k = seq v1 $ seq v2 $ unId $ (f <<< (M:|Strng v1:|Strng v2) ... h)
                      (Z:.pointLI 10:.pointLI 10) (Z:.pointLI k:.pointLI k)
  where f (Z:.zs:.qs) = VU.sum (VU.map ord zs VU.++ VU.map ord qs)
        h   = S.foldl' (+) 0
{-# NoInline stream_Strng_V #-}

stream_Strng2_S :: Int -> Int
stream_Strng2_S k = seq v1 $ seq v2 $
                    unId $ (f <<< Strng v1 % Strng v2 ... h)
                    (pointLI 10) (pointLI k)
  where f qs zs = VU.length qs + VU.length zs -- VU.sum (VU.map ord qs VU.++ VU.map ord zs)
        h   = S.foldl' (+) 0
{-# NoInline stream_Strng2_S #-}
 
stream_Strng2_V :: Int -> Int -> Int
stream_Strng2_V k l = seq v1 $ seq v2 $
                    unId $ (f <<< (M:|Strng v1:|Epsilon) % (M:|Strng v2:|Epsilon) ... h)
                      (Z:.pointLI 10:.pointLI 10) (Z:.pointLI k:.pointLI l)
  where f (Z:.qs:.()) (Z:.zs:.()) = VU.length qs + VU.length zs
        h   = S.foldl' (+) 0
        {-# Inline f #-}
        {-# Inline h #-}
{-# NoInline stream_Strng2_V #-}



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

