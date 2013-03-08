{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Tests.QuickCheck where

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

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion
import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.Region
import ADP.Fusion.Table
import ADP.Fusion.Term


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

-- | A single mutable table should return one result.

prop_Mt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mtable mxs
    zs <- run $ id <<< mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.sw)) | i<=j]
    assert $ zs == ls

-- | table, then character.

prop_MtC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % Chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword i (j-1))) >>= \a -> return (a,xs VU.! (j-1)) | i<j]
    assert $ zs == ls

-- | Character, then table.

prop_CMt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mtable mxs
    zs <- run $ (,) <<< Chr xs % mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword (i+1) j)) >>= \a -> return (xs VU.! i,a) | i<j]
    assert $ zs == ls

-- | Two mutable tables. Basically like Region's.

prop_MtMt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword i k)) >>= \a -> PA.readM mxs (Z:.subword k j) >>= \b -> return (a,b) | k <- [i..j]]
    assert $ zs == ls

-- | Just to make it more interesting, sprinkle in some 'Chr' symbols.

prop_CMtCMtC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mtable mxs
    zs <- run $ (,,,,) <<< Chr xs % mt % Chr xs % mt % Chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [ (PA.readM mxs (Z:.subword (i+1) k)) >>=
                            \a -> PA.readM mxs (Z:.subword (k+1) (j-1)) >>=
                            \b -> return ( xs VU.! i
                                         , a
                                         , xs VU.! k
                                         , b
                                         , xs VU.! (j-1)
                                         )
                           | k <- [i+1..j-2]]
    assert $ zs == ls

-- | And now with non-empty tables.

prop_CMnCMnC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = MTable Tsome mxs
    zs <- run $ (,,,,) <<< Chr xs % mt % Chr xs % mt % Chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [ (PA.readM mxs (Z:.subword (i+1) k)) >>=
                            \a -> PA.readM mxs (Z:.subword (k+1) (j-1)) >>=
                            \b -> return ( xs VU.! i
                                         , a
                                         , xs VU.! k
                                         , b
                                         , xs VU.! (j-1)
                                         )
                           | k <- [i+2..j-3]]
    assert $ zs == ls

-- | Our first multi-tape terminal ":-)"

prop_Tt ix@Z = zs == ls where
  zs = id <<< Term T ... S.toList $ ix
  ls = [ Z ]

-- | Increase dimension by 1. (1-tape grammars)

prop_Tc ix@(Z:.Subword(i:.j)) = zs == ls where
  zs = id <<< Term (T:.Chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i) | i+1==j ]

prop_Mt_Tc ix@(Z:.Subword(i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ]
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % Term (T:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword i (j-1))) >>= \a -> return (a,Z:.xs VU.! (j-1)) | i<j ]
    assert $ zs == ls

-- | and with 2-tape grammars

prop_Tcc ix@(Z:.Subword(i:.j):.Subword(k:.l)) = zs == ls where
  zs = id <<< Term (T:.Chr xs:.Chr xs) ... S.toList $ ix
  ls = [ (  Z
         :. xs VU.! i
         :. xs VU.! k
         ) | i+1==j, k+1==l ]

prop_Mt_Tcc (Z:.TinySubword (i:.j):.TinySubword (k:.l)) = monadicIO $ do
    let ix = Z :. subword i j :. subword k l
    mxs :: (PA.MU IO (Z:.Subword:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0):.Subword(0:.0)) (Z:. Subword (0:.j+1):.Subword (0:.k+1)) [0 .. ]
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % Term (T:.Chr xs:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [ (PA.readM mxs (Z:.subword i (j-1):.subword k (l-1))) >>= \a -> return (a,Z:.xs VU.! (j-1):.xs VU.! (l-1)) | i<j,k<l ]
    assert $ zs == ls


{-
gnargs (Z:.TinySubword (i:.j)) = do
    let ix = Z :. subword i j
    mxs :: (PA.MU IO (Z:.Subword) Int) <- PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ]
    let mt = mtable mxs
    zs <- (\x (Z:.a) -> x+a) <<< mt % Term (T:.Chr xs) ... SM.foldl' (+) 0 $ ix
    ix `seq` mxs `seq` mt `seq` return zs
{-# NOINLINE gnargs #-}
-}

-- | and with 3-tape grammars

prop_Tccc ix@(Z:.Subword(i:.j):.Subword(k:.l):.Subword(a:.b)) = zs == ls where
  zs = id <<< Term (T:.Chr xs:.Chr xs:.Chr xs) ... S.toList $ ix
  ls = [ (  Z
         :. xs VU.! i
         :. xs VU.! k
         :. xs VU.! a
         ) | i+1==j, k+1==l, a+1==b ]

-- * helper functions and stuff

-- | Helper function to create non-specialized regions

region = Region Nothing Nothing

-- |

mtable xs = MTable Tmany xs

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

newtype TinySubword = TinySubword (Int:.Int)
  deriving (Show)

instance Arbitrary TinySubword where
  arbitrary = do a <- choose (0,20)
                 b <- choose (0,20)
                 return $ TinySubword $ min a b :. max a b
  shrink (TinySubword (a:.b)) = [TinySubword (a:.b-1) | a<b]

instance Arbitrary z => Arbitrary (z:.TinySubword) where
  arbitrary = (:.) <$> arbitrary <*> arbitrary
  shrink (z:.s) = (:.) <$> shrink z <*> shrink s

