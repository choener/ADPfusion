{-# LANGUAGE PackageImports #-}

module ADP.Fusion.QuickCheck.Arbitrary where

import Test.QuickCheck
import Test.QuickCheck.All

import "PrimitiveArray" Data.Array.Repa.Index

import qualified ADP.Fusion.Monadic.Internal as F

lAchar (i,j) = [j | i+1 == j]

-- |
--
-- NOTE we have to add 1 to the i-index. Legacy ADP reads chars from an input
-- array starting at "1", while ADPfusion starts arrays at "0".

fAchar :: DIM2 -> (F.Scalar Int)
fAchar (Z:.i:.j) = F.Scalar $ (i+1)

fRegion :: DIM2 -> (F.Scalar (Int,Int))
fRegion (Z:.i:.j) = F.Scalar $ (i,j)

-- * quickcheck stuff

newtype Small = Small Int
  deriving (Show)

instance Arbitrary Small where
  arbitrary = Small `fmap` choose (0,50)
  shrink (Small x)
    | x>0       = [Small $ x-1]
    | otherwise = []

small x = x>=0 && x <=50

(===) f g (Small i, Small j) = f (i,j) == g (i,j)

