{-# LANGUAGE PackageImports #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | QuickCheck properties for a number of ADPfusion combinators.

module Tests.Core where

import "PrimitiveArray" Data.Array.Repa.Index
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import Data.Vector.Fusion.Stream (Stream)
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Unboxed as VU
import Data.List

import ADP.Fusion
import qualified ADP.Fusion.Monadic as M
import qualified ADP.Fusion.Monadic.Internal as F



fun4 :: Int -> Int -> Int -> Int -> Int
fun4 w x y z = w+x+y+z
{-# INLINE fun4 #-}

f :: Int -> Int -> Int -> Int
f a b c = a+b+c
{-# INLINE f #-}

g :: Int -> Int
g a = a+999
{-# INLINE g #-}

h :: Stream Int -> Int
h = S.foldl' (+) 0
{-# INLINE h #-}

ws, xs, ys, zs :: DIM2 -> Scalar Int
ws (Z:.i:.j) = Scalar $ i+j+737
xs (Z:.i:.j) = Scalar $ i+j+23
ys (Z:.i:.j) = Scalar $ i+j+42
zs (Z:.i:.j) = Scalar $ i+j+123
{-# INLINE ws #-}
{-# INLINE xs #-}
{-# INLINE ys #-}
{-# INLINE zs #-}

stream4 :: Int -> Int -> Int
stream4 i j = fun4 <<< ws +~+ xs +~+ ys +~+ zs ... h $ Z:.i:.j
{-# INLINE stream4 #-}

theCore4 i j = stream4 i j
{-# NOINLINE theCore4 #-}

{-
stream3 :: Int -> Int -> Int
stream3 i j = f <<< xs +~+ ys +~+ zs ... h $ Z:.i:.j
{-# INLINE stream3 #-}

theCore3 i j = stream3 i j
{-# NOINLINE theCore3 #-}
-}

{-
stream2 :: Int -> Int -> Int
stream2 i j = (+) <<< xs +~+ ys ... h $ Z:.i:.j
{-# INLINE stream2 #-}

theCore2 i j = stream2 i j
{-# NOINLINE theCore2 #-}
-}

{-
stream1 :: Int -> Int -> Int
stream1 i j = g <<< xs ... h $ Z:.i:.j
{-# INLINE stream1 #-}

theCore1 i j = stream1 i j
{-# NOINLINE theCore1 #-}
-}

