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
import Debug.Trace

import Data.Array.Repa.Index.Subword

import ADP.Fusion
import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.Region

-- | Check if a single region returns the correct result (namely a slice from
-- the input).

prop_R sw@(Subword (i:.j)) = zs == ls where
  zs = id <<< region xs ... S.toList $ sw
  ls = [VU.slice i (j-i) xs]

-- | Two regions next to each other.

prop_RR sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< region xs % region xs ... S.toList $ sw
  ls = [(VU.slice i (k-i) xs, VU.slice k (j-k) xs) | k <- [i..j]]

-- | And finally, three regions (with smaller subword sizes only)

prop_RRR sw@(Subword (i:.j)) = (j-i<=30) ==> zs == ls where
  zs = (,,) <<< region xs % region xs % region xs ... S.toList $ sw
  ls = [  ( VU.slice i (k-i) xs
          , VU.slice k (l-k) xs
          , VU.slice l (j-l) xs
          ) | k <- [i..j], l <- [k..j]]

-- | Single-character parser.

prop_C sw@(Subword (i:.j)) = zs == ls where
  zs = id <<< Chr xs ... S.toList $ sw
  ls = [xs VU.! i | i+1==j]

-- | 2x Single-character parser.

prop_CC sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< Chr xs % Chr xs ... S.toList $ sw
  ls = [(xs VU.! i, xs VU.! (i+1)) | i+2==j]

-- | 2x Single-character parser bracketing a single region.

prop_CRC sw@(Subword (i:.j)) = zs == ls
  where
    zs = (,,) <<< Chr xs % region xs % Chr xs ... S.toList $ sw
    ls = [(xs VU.! i, VU.slice (i+1) (j-i-2) xs , xs VU.! (j-1)) |i+2<=j]


-- | 2x Single-character parser bracketing regions.

prop_CRRC sw@(Subword (i:.j)) = zs == ls
  where
    zs = (,,,) <<< Chr xs % region xs % region xs % Chr xs ... S.toList $ sw
    ls = [ ( xs VU.! i
           , VU.slice (i+1) (k-i-1) xs
           , VU.slice k (j-k-1) xs
           , xs VU.! (j-1)
           ) | k <- [i+1 .. j-1]]

-- | complex behaviour with characters and regions

prop_CRCRC sw@(Subword (i:.j)) = zs == ls where
  zs = (,,,,) <<< Chr xs % region xs % Chr xs % region xs % Chr xs ... S.toList $ sw
  ls = [ ( xs VU.! i
         , VU.slice (i+1) (k-i-1) xs
         , xs VU.! k
         , VU.slice (k+1) (j-k-2) xs
         , xs VU.! (j-1)
         ) | k <- [i+1 .. j-2] ]

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

