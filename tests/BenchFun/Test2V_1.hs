
{-# Options_GHC -fmax-worker-args=25 #-}
{-# Options_GHC -fforce-recomp #-}

module BenchFun.Test2V_1 where

import Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Util
import Data.Vector.Unboxed as VU
import Debug.Trace
import Data.Char (ord)

import ADP.Fusion.Point
import ADP.Fusion.Term.Test.Point
import ADP.Fusion.Term.Test.Type
import Data.PrimitiveArray hiding (map, unsafeIndex)

import BenchFun.Common



stream_Test2_V_1 :: Int -> Int -> Int
stream_Test2_V_1 k l = seq v1 $ seq v2 $ seq v3 $ seq v4 $
                        unId $ (f <<< (M:|Test v1:|Test v3) % (M:|Test v2:|Test v4) ... h)
                          (Z:.pointLI 140:.pointLI 140) (Z:.pointLI k:.pointLI l)
  where f (Z:.as:.cs) (Z:.bs:.ds) = VU.length as + VU.length bs + VU.length cs + VU.length ds
        h   = S.foldl' (+) 0
        {-# Inline f #-}
        {-# Inline h #-}
{-# NoInline stream_Test2_V_1 #-}

