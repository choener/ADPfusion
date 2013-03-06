{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Tests.QuickCheck where

import Control.Applicative
import Test.QuickCheck
import Test.QuickCheck.All
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Unboxed as VU
import Data.Array.Repa.Index
import Data.Array.Repa.Shape

import Data.Array.Repa.Index.Subword

import ADP.Fusion
import ADP.Fusion.Classes
import ADP.Fusion.Region

-- | Check if a single region returns the correct result (namely a slice from
-- the input).

prop_R sw@(Subword (i:.j)) = zs == ls where
  -- fusion
  zs :: [VU.Vector Int]
  zs = id <<< region xs ... S.toList $ sw
  -- handwritten list
  ls = [VU.slice i (j-i) xs]

-- | Two regions next to each other.

prop_RR sw@(Subword (i:.j)) = zs == ls where
  zs :: [(VU.Vector Int,VU.Vector Int)]
  zs = (,) <<< region xs % region xs ... S.toList $ sw
  ls = [(VU.slice i (k-i) xs, VU.slice k (j-k) xs) | k <- [i..j]]

-- | And finally, three regions

prop_RRR sw@(Subword (i:.j)) = zs == ls where
--  zs :: [(VU.Vector Int,VU.Vector Int)]
  zs = (,,) <<< region xs % region xs % region xs ... S.toList $ sw
  ls = [  ( VU.slice i (k-i) xs
          , VU.slice k (l-k) xs
          , VU.slice l (j-l) xs
          ) | k <- [i..j], l <- [k..j]]

-- |

-- | Helper function to create non-specialized regions

region = Region Nothing Nothing

-- | data set. Can be made fixed as the maximal subword size is statically known!

xs = VU.fromList [0 .. 100 :: Int]

{-
-- | A subword (i,j) should always produce an index in the allowed range

prop_subwordIndex (Small n, Subword (i:.j)) = (n>j) ==> p where
  p = n * (n+1) `div` 2 >= k
  k = subwordIndex (subword 0 n) (subword i j)
-}



-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

allProps = $forAllProperties customCheck



newtype Small = Small Int
  deriving (Show)

instance Arbitrary Small where
  arbitrary = Small <$> choose (0,100)
  shrink (Small i) = Small <$> shrink i

