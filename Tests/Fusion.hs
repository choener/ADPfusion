{-# LANGUAGE TypeOperators #-}

module Tests.Fusion where

import Control.Applicative
import Data.Array.Repa.Index
import Data.Array.Repa.Shape
import Data.Array.Repa.Arbitrary
import Debug.Trace
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import Test.QuickCheck
import Test.QuickCheck.All
import Test.QuickCheck.Monadic
import Data.List ((\\))

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Point
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion



testF :: Int -> Int -> Int
testF i j =
  p6 <<< peekL testVs % chr testVs % Tbl testA % sregion 3 10 testVs % chr testVs % peekR testVs |||
  p6 <<< peekR testVs % chr testVs % Tbl testA % sregion 3 10 testVs % chr testVs % peekL testVs ... (S.foldl' (+) 0) $ subword i j
{-# NOINLINE testF #-}

p6 a b c d e f = a+b+c+ VU.maximum d +e+f

{-
testG :: Int -> Int -> Int
testG i j =
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs |||
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs ... (Sp.foldl' (+) 0) $ subword i j
{-# NOINLINE testG #-}
-}

testA :: PA.Unboxed (Z:.Subword) Int
testA = PA.fromAssocs (Z:.subword 0 0) (Z:.subword 0 50) 0 []
{-# NOINLINE testA #-}

testVs :: VU.Vector Int
testVs = VU.fromList [ 0 .. 9999 ]
{-# NOINLINE testVs #-}

{-
--gugg :: Int -> Int -> [(Int,VU.Vector Int,Int)]
gugg i j = (,,) <<< chrR testVs % region testVs % chrL testVs ... Sp.toList $ subword i j
-}
