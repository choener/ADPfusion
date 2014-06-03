{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module ADP.Fusion.QuickCheck where

import Control.Monad
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
import System.IO.Unsafe

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Point
import Data.Array.Repa.Index.Points
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion
import ADP.Fusion.Chr
import ADP.Fusion.Classes as ADP
import ADP.Fusion.Empty
import ADP.Fusion.Multi
import ADP.Fusion.Multi.Classes
import ADP.Fusion.None
import ADP.Fusion.Table



{-

-- | Check if a single region returns the correct result (namely a slice from
-- the input).

prop_R sw@(Subword (i:.j)) = zs == ls where
  zs = id <<< region xs ... S.toList $ sw
  ls = [VU.slice i (j-i) xs | i>=0, j<=100]

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

-- | Three sized regions (with smaller subword sizes only)

prop_SSS sw@(Subword (i:.j)) = zs == ls where
  zs = (,,) <<< sregion 3 10 xs % sregion 3 10 xs % sregion 3 10 xs ... S.toList $ sw
  ls = [  ( VU.slice i (k-i) xs
          , VU.slice k (l-k) xs
          , VU.slice l (j-l) xs
          ) | k <- [i..j], l <- [k..j], minimum [k-i,l-k,j-l] >=3, maximum [k-i,l-k,j-l] <= 10]

-}

-- | Single-character parser.

prop_C sw@(Subword (i:.j)) = zs == ls where
  zs = id <<< chr xs ... S.toList $ sw
  ls = [xs VU.! i | i+1==j, i>=0, j<=100]

-- | 2x Single-character parser.

prop_CC sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< chr xs % chr xs ... S.toList $ sw
  ls = [(xs VU.! i, xs VU.! (i+1)) | i+2==j]

{-

-- ** Single character plus peeking

prop_PlC sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< peekL xs % chr xs ... S.toList $ sw
  ls = [(xs VU.! (j-2), xs VU.! (j-1)) | j>1, i+1==j]

prop_PrC sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< peekR xs % chr xs ... S.toList $ sw
  ls = [(xs VU.! (j-1), xs VU.! (j-1)) | i+1==j]

prop_CPr sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< chr xs % peekR xs ... S.toList $ sw
  ls = [(xs VU.! (j-1), xs VU.! j) | i>=0, j<=99,i+1==j]

prop_CPl sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< chr xs % peekL xs ... S.toList $ sw
  ls = [(xs VU.! (j-1), xs VU.! (j-1)) | i+1==j]

-- | 2x Single-character parser bracketing a single region.

prop_CRC sw@(Subword (i:.j)) = zs == ls
  where
    zs = (,,) <<< chr xs % region xs % chr xs ... S.toList $ sw
    ls = [(xs VU.! i, VU.slice (i+1) (j-i-2) xs , xs VU.! (j-1)) |i+2<=j]

-- | 2x Single-character parser bracketing regions.

prop_CRRC sw@(Subword (i:.j)) = zs == ls
  where
    zs = (,,,) <<< chr xs % region xs % region xs % chr xs ... S.toList $ sw
    ls = [ ( xs VU.! i
           , VU.slice (i+1) (k-i-1) xs
           , VU.slice k (j-k-1) xs
           , xs VU.! (j-1)
           ) | k <- [i+1 .. j-1]]

-- | complex behaviour with characters and regions

prop_CRCRC sw@(Subword (i:.j)) = zs == ls where
  zs = (,,,,) <<< chr xs % region xs % chr xs % region xs % chr xs ... S.toList $ sw
  ls = [ ( xs VU.! i
         , VU.slice (i+1) (k-i-1) xs
         , xs VU.! k
         , VU.slice (k+1) (j-k-2) xs
         , xs VU.! (j-1)
         ) | k <- [i+1 .. j-2] ]

-- | Interior-loop like structures.

prop_Interior1 sw@(Subword (i:.j)) = zs == ls where
  zs = (,,) <<< chr xs % peekR xs % sregion 1 5 xs ... S.toList $ sw
  ls = [ ( xs VU.! i
         , xs VU.! (i+1)
         , VU.slice (i+1) (j-i-1) xs
         ) | j-i>=2, j-i<=6
       ]

prop_Interior2 sw@(Subword (i:.j)) = zs == ls where
  zs = (,,,,) <<< chr xs % peekR xs % sregion 1 5 xs % peekR xs % sregion 2 5 xs ... S.toList $ sw
  ls = [ ( xs VU.! i
         , xs VU.! (i+1)
         , VU.slice (i+1) (k-i-1) xs
         , xs VU.! k
         , VU.slice k (j-k) xs
         ) | j-i>=4, j-i<=11, k <- [i+2 .. (min j $ i+6)], j-k>=2, j-k<=5
       ]

prop_Interior3 sw@(Subword (i:.j)) = zs == ls where
  zs = (,,,,,,) <<< chr xs % peekR xs % sregion 1 5 xs % peekR xs % sregion 2 5 xs % peekL xs % sregion 1 5 xs ... S.toList $ sw
  ls = [ ( xs VU.! i
         , xs VU.! (i+1)
         , VU.slice (i+1) (k-i-1) xs
         , xs VU.! k
         , VU.slice k (l-k) xs
         , xs VU.! (l-1)
         , VU.slice l (j-l) xs
         ) | i>= 0
           , j<= 100
           , k <- [i..j]
           , l <- [k..j]
           , j-i>=5, j-i<=16
           , k-i-1>=1, k-i-1<=5
           , l-k>=2, l-k<=5
           , j-l>=1, j-l<=5
       ]

prop_Interior4 sw@(Subword (i:.j)) = zs == ls where
  zs = (,,,,,,,,) <<< chr xs % peekR xs % sregion 1 5 xs % peekR xs % sregion 2 5 xs % peekL xs % sregion 1 5 xs % peekL xs % chr xs ... S.toList $ sw
  ls = [ ( xs VU.! i
         , xs VU.! (i+1)
         , VU.slice (i+1) (k-i-1) xs
         , xs VU.! k
         , VU.slice k (l-k) xs
         , xs VU.! (l-1)
         , VU.slice l (j-l-1) xs
         , xs VU.! (j-2)
         , xs VU.! (j-1)
         ) | k <- [i..j]
           , l <- [k..j]
           , j-i>=6, j-i<=17
           , k-i-1>=1, k-i-1<=5
           , l-k>=2, l-k<=5
           , j-l-1>=1, j-l-1<=5
       ]

prop_Interior5 sw@(Subword (i:.j)) = zs == ls where
  zs = (,,,,,,,,,,) <<< peekL xs % chr xs % peekR xs % sregion 1 5 xs % peekR xs % sregion 2 5 xs % peekL xs % sregion 1 5 xs % peekL xs % chr xs % peekR xs ... S.toList $ sw
  ls = [ ( xs VU.! (i-1)
         , xs VU.! i
         , xs VU.! (i+1)
         , VU.slice (i+1) (k-i-1) xs
         , xs VU.! k
         , VU.slice k (l-k) xs
         , xs VU.! (l-1)
         , VU.slice l (j-l-1) xs
         , xs VU.! (j-2)
         , xs VU.! (j-1)
         , xs VU.! j
         ) | i>= 1
           , j<= 99
           , k <- [i..j]
           , l <- [k..j]
           , i>0, j-1 < VU.length xs
           , j-i>=6, j-i<=17
           , k-i-1>=1, k-i-1<=5
           , l-k>=2, l-k<=5
           , j-l-1>=1, j-l-1<=5
       ]

-}

-- | A single mutable table should return one result.

prop_Mt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: PA.MutArr IO (PA.Unboxed Subword Int) <- run $ PA.fromListM (Subword (0:.0)) (Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblS EmptyOk mxs
    zs <- run $ id <<< mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs sw) | i<=j]
    assert $ zs == ls


-- | table, then character.

prop_MtC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed Subword Int)) <- run $ PA.fromListM (Subword (0:.0)) (Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblS EmptyOk mxs
    zs <- run $ (,) <<< mt % chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (subword i (j-1))) >>= \a -> return (a,xs VU.! (j-1)) | i<j]
    assert $ zs == ls

-- | Character, then table.

prop_CMt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed Subword Int)) <- run $ PA.fromListM (Subword (0:.0)) (Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblS EmptyOk mxs
    zs <- run $ (,) <<< chr xs % mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (subword (i+1) j)) >>= \a -> return (xs VU.! i,a) | i<j]
    assert $ zs == ls

-- | Two mutable tables. Basically like Region's.

prop_MtMt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed Subword Int)) <- run $ PA.fromListM (Subword (0:.0)) (Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblS EmptyOk mxs
    zs <- run $ (,) <<< mt % mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (subword i k)) >>= \a -> PA.readM mxs (subword k j) >>= \b -> return (a,b) | k <- [i..j]]
    assert $ zs == ls

-- | Just to make it more interesting, sprinkle in some 'Chr' symbols.

prop_CMtCMtC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed Subword Int)) <- run $ PA.fromListM (Subword (0:.0)) (Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblS EmptyOk mxs
    zs <- run $ (,,,,) <<< chr xs % mt % chr xs % mt % chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [ (PA.readM mxs (subword (i+1) k)) >>=
                            \a -> PA.readM mxs (subword (k+1) (j-1)) >>=
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
    mxs :: (PA.MutArr IO (PA.Unboxed Subword Int)) <- run $ PA.fromListM (Subword (0:.0)) (Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblS ADP.NonEmpty mxs
    zs <- run $ (,,,,) <<< chr xs % mt % chr xs % mt % chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [ (PA.readM mxs (subword (i+1) k)) >>=
                            \a -> PA.readM mxs (subword (k+1) (j-1)) >>=
                            \b -> return ( xs VU.! i
                                         , a
                                         , xs VU.! k
                                         , b
                                         , xs VU.! (j-1)
                                         )
                           | k <- [i+2..j-3]]
    assert $ zs == ls

{-

-- **

prop_Tc ix@(Z:.Subword(i:.j)) = zs == ls where
  zs = id <<< (T:!chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i) | i>=0, j<= 100, i+1==j ]

prop_Tcc ix@(Z:.Subword(i:.j):.Subword(k:.l)) = zs == ls where
  zs = id <<< (T:!chr xs:!chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i:.xs VU.! k) | i>=0, j<=100, k>=0, j<=100, i+1==j, k+1==l ]

-- **

prop_TcTc ix@(Z:.Subword(i:.j)) = zs == ls where
  zs = (,) <<< (T:!chr xs) % (T:!chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i,Z:.xs VU.! (i+1)) | i>=0, j<= 100, i+2==j ]

prop_TccTcc ix@(Z:.Subword(i:.j):.Subword(k:.l)) = zs == ls where
  zs = (,) <<< (T:!chr xs:!chr xs) % (T:!chr xs:!chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i:.xs VU.! k, Z:.xs VU.! (i+1):.xs VU.! (k+1)) | i>=0, j<=100, k>=0, j<=100, i+2==j, k+2==l ]

-- **

prop_Mt2 ix@(Z:.Subword(i:.j)) = monadicIO $ do
  mxs :: PA.MutArr IO (PA.Unboxed (Z:.Subword) Int) <- run $ PA.fromListM (Z:.subword 0 0) (Z:.subword 0 100) [0 ..]
  let mt = mTbl (Z:.EmptyT) mxs -- :: MTbl (Z:.Subword) (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int))
  zs <- run $ id <<< mt ... SM.toList $ ix
  ls <- run $ sequence $ [ (PA.readM mxs (Z:.subword i j)) | i>=0, j<=100, i<=j ]
  assert $ zs == ls

prop_MtMt2 ix@(Z:.Subword(i:.j)) = monadicIO $ do
  mxs :: PA.MutArr IO (PA.Unboxed (Z:.Subword) Int) <- run $ PA.fromListM (Z:.subword 0 0) (Z:.subword 0 100) [0 ..]
  let mt = mTbl (Z:.EmptyT) mxs -- :: MTbl (Z:.Subword) (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int))
  zs <- run $ (,) <<< mt % mt ... SM.toList $ ix
  ls <- run $ sequence $ [ liftM2 (,) (PA.readM mxs (Z:.subword i k)) (PA.readM mxs (Z:.subword k j)) | i>=0, j<=100, k<-[i..j] ]
  assert $ zs == ls

prop_MtMtMt2 ix@(Z:.Subword(i:.j)) = monadicIO $ do
  mxs :: PA.MutArr IO (PA.Unboxed (Z:.Subword) Int) <- run $ PA.fromListM (Z:.subword 0 0) (Z:.subword 0 100) [0 ..]
  let mt = mTbl (Z:.EmptyT) mxs -- :: MTbl (Z:.Subword) (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int))
  zs <- run $ (,,) <<< mt % mt % mt ... SM.toList $ ix
  ls <- run $ sequence $ [ liftM3 (,,) (PA.readM mxs (Z:.subword i k)) (PA.readM mxs (Z:.subword k l)) (PA.readM mxs (Z:.subword l j)) | i>=0, j<=100, k<-[i..j], l<-[k..j] ]
  assert $ zs == ls

prop_TcMtTc ix@(Z:.Subword(i:.j)) = monadicIO $ do
  mxs :: PA.MutArr IO (PA.Unboxed (Z:.Subword) Int) <- run $ PA.fromListM (Z:.subword 0 0) (Z:.subword 0 100) [0 ..]
  let mt = mTbl (Z:.EmptyT) mxs :: MTbl (Z:.Subword) (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int))
  zs <- run $ (,,) <<< (T:!chr xs) % mt % (T:!chr xs) ... SM.toList $ ix
  ls <- run $ sequence $ [ (PA.readM mxs (Z:.subword (i+1) (j-1)) >>= \z -> return (Z:.xs VU.! i,z,Z:.xs VU.! (j-1))) | i>=0, j<=100, i+2<=j ]
  assert $ zs == ls

prop_2dim ix@(Z:.TinySubword(i:.j):.TinySubword(k:.l)) = monadicIO $ do
  mxs <- run $ pure $ mxsSwSw
  let mt = mTbl (Z:.EmptyT:.EmptyT) mxs
  zs <- run $ (,) <<< mt % mt ... SM.toList $ Z:.subword i j:.subword k l
  ls <- run $ sequence $ [ liftM2 (,) (PA.readM mxs (Z:.subword i a:.subword k b)) (PA.readM mxs (Z:.subword a j:.subword b l)) | i>=0, j<=100, k>=0, l<=100, a<-[i..j], b<-[k..l] ]
  assert $ zs==ls

prop_2dimCMCMC ix@(Z:.TinySubword(i:.j):.TinySubword(k:.l)) = monadicIO $ do
  mxs <- run $ pure $ mxsSwSw -- :: PA.MutArr IO (PA.Unboxed (Z:.Subword:.Subword) Int) <- run $ PA.fromListM (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 100:.subword 0 100) [0 ..]
  let mt = mTbl (Z:.EmptyT:.EmptyT) mxs
  zs <- run $ (,,,,) <<< (T:!chr xs:!chr xs) % mt % (T:!chr xs:!chr xs) % mt % (T:!chr xs:!chr xs) ... SM.toList $ Z:.subword i j:.subword k l
  ls <- run $ sequence $ [ liftM5 (,,,,) (pure $ Z:.xs VU.! i:.xs VU.! k)
                                         (PA.readM mxs (Z:.subword (i+1) a:.subword (k+1) b))
                                         (pure $ Z:.xs VU.! a:.xs VU.! b)
                                         (PA.readM mxs (Z:.subword (a+1) (j-1):.subword (b+1) (l-1)))
                                         (pure $ Z:.xs VU.! (j-1):.xs VU.! (l-1))
                         | j-i>=3, l-k>=3, i>=0, j<=100, k>=0, l<=100, a<-[i+1..j-2], b<-[k+1..l-2] ]
  assert $ zs==ls

-}

-- * working on 'PointL's

prop_P_Tt ix@(Z:.PointL (i:.j)) = zs == ls where
  zs = id <<< (M:>chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i) | i+1==j ]

prop_P_CC ix@(Z:.PointL (i:.j)) = zs == ls where
  zs = (,) <<< (M:>chr xs) % (M:>chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! i, Z:.xs VU.! (i+1)) | i+2==j ]

-- |
--
-- TODO need to synchronize the constraints in @ls@ and in 'PointL'

prop_P_2dimMtCC ix@(Z:.PointL(i:.j):.PointL(k:.l)) = monadicIO $ do
--  let ix@(Z:.PointL(i:.j):.PointL(k:.l)) = (Z:.pointL 0 3:.pointL 0 3)
  mxs <- run $ pure $ mxsPP
  let mt = mTblD (Z:.EmptyOk:.EmptyOk) mxs
  zs <- run $ (,,) <<< mt % (M:>chr xs:>chr xs) % (M:>chr xs:>chr xs) ... SM.toList $ ix
  ls <- run $ sequence $ [ liftM3 (,,)   (PA.readM mxs (Z:.pointL i (j-2):.pointL k (l-2)))
                                         (pure $ Z:.xs VU.! (j-2):.xs VU.! (l-2))
                                         (pure $ Z:.xs VU.! (j-1):.xs VU.! (l-1))
                         | j-i>=2, l-k>=2, i==0, j<=100, k==0, l<=100] --, a<-[i+1..j-2], b<-[k+1..l-2] ]
  if zs==ls
    then assert $ zs==ls
    else traceShow (zs,ls) $ assert False

-- |
--
-- This property WILL FAIL, because we do not protect against the stupidity of
-- embedding tables between characters.
--
-- TODO And actually the @ls@ part is incorrect anyway, since it should be @[]@
-- legally speaking.
{-
prop_P_2dimCMCMC () = monadicIO $ do -- ix@(Z:.PointL(i:.j):.PointL(k:.l)) = monadicIO $ do
  let ix@(Z:.PointL(i:.j):.PointL(k:.l)) = (Z:.pointL 0 3:.pointL 0 3)
  mxs <- run $ pure $ mxsPP
  let mt = mTblD (Z:.EmptyOk:.EmptyOk) mxs
  zs <- run $ (,,,,) <<< (M:>chr xs:>chr xs) % mt % (M:>chr xs:>chr xs) % mt % (M:>chr xs:>chr xs) ... SM.toList $ ix
  ls <- run $ sequence $ [ liftM5 (,,,,) (pure $ Z:.xs VU.! i:.xs VU.! k)
                                         (PA.readM mxs (Z:.pointL (i+1) a:.pointL (k+1) b))
                                         (pure $ Z:.xs VU.! a:.xs VU.! b)
                                         (PA.readM mxs (Z:.pointL (a+1) (j-1):.pointL (b+1) (l-1)))
                                         (pure $ Z:.xs VU.! (j-1):.xs VU.! (l-1))
                         | j-i>=3, l-k>=3, i>=0, j<=100, k>=0, l<=100, a<-[i+1..j-2], b<-[k+1..l-2] ]
  if zs==ls
    then assert $ zs==ls
    else traceShow (zs,ls) $ assert False
-}

-- * helper functions and stuff

-- | A subword (i,j) should always produce an index in the allowed range

prop_subwordIndex (SmallInt n, Subword (i:.j)) = (n>j) ==> p where
  p = n * (n+1) `div` 2 >= k
  k = subwordIndex (subword 0 n) (subword i j)

-- | data set. Can be made fixed as the maximal subword size is statically known!

xs = VU.fromList [0 .. 99 :: Int]

--
--
--TODO will break if PrimitiveArray assertions are active (need to fixe exact length of list)

mxsSwSw = unsafePerformIO $ zzz where
  zzz :: IO (PA.MutArr IO (PA.Unboxed (Z:.Subword:.Subword) Int))
  zzz = PA.fromListM (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 100:.subword 0 100) [0 ..]

mxsPP = unsafePerformIO $ zzz where
  zzz :: IO (PA.MutArr IO (PA.Unboxed (Z:.PointL:.PointL) Int))
  zzz = PA.fromListM (Z:.pointL 0 0:.pointL 0 0) (Z:.pointL 0 100:.pointL 0 100) [0 ..]




newtype SmallInt = SmallInt Int
  deriving (Show)

instance Arbitrary SmallInt where
  arbitrary = SmallInt <$> choose (0,100)
  shrink (SmallInt i) = SmallInt <$> shrink i

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



-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

