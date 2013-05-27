{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module ADP.Fusion.QuickCheck where

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
import ADP.Fusion.Table
import ADP.Fusion.Multi


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

-- | Single-character parser.

prop_C sw@(Subword (i:.j)) = zs == ls where
  zs = id <<< chr xs ... S.toList $ sw
  ls = [xs VU.! i | i+1==j, i>=0, j<=100]

-- | 2x Single-character parser.

prop_CC sw@(Subword (i:.j)) = zs == ls where
  zs = (,) <<< chr xs % chr xs ... S.toList $ sw
  ls = [(xs VU.! i, xs VU.! (i+1)) | i+2==j]

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

-- | A single mutable table should return one result.

prop_Mt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: PA.MutArr IO (PA.Unboxed (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblSw EmptyT mxs
    zs <- run $ id <<< mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.sw)) | i<=j]
    assert $ zs == ls

-- | table, then character.

prop_MtC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int)) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblSw EmptyT mxs
    zs <- run $ (,) <<< mt % chr xs ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword i (j-1))) >>= \a -> return (a,xs VU.! (j-1)) | i<j]
    assert $ zs == ls

-- | Character, then table.

prop_CMt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int)) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblSw EmptyT mxs
    zs <- run $ (,) <<< chr xs % mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword (i+1) j)) >>= \a -> return (xs VU.! i,a) | i<j]
    assert $ zs == ls

-- | Two mutable tables. Basically like Region's.

prop_MtMt sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int)) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblSw EmptyT mxs
    zs <- run $ (,) <<< mt % mt ... SM.toList $ sw
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword i k)) >>= \a -> PA.readM mxs (Z:.subword k j) >>= \b -> return (a,b) | k <- [i..j]]
    assert $ zs == ls

-- | Just to make it more interesting, sprinkle in some 'Chr' symbols.

prop_CMtCMtC sw@(Subword (i:.j)) = monadicIO $ do
    mxs :: (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int)) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblSw EmptyT mxs
    zs <- run $ (,,,,) <<< chr xs % mt % chr xs % mt % chr xs ... SM.toList $ sw
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
    mxs :: (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int)) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ] -- (1 :: Int)
    let mt = mTblSw NonEmptyT mxs
    zs <- run $ (,,,,) <<< chr xs % mt % chr xs % mt % chr xs ... SM.toList $ sw
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

{-
 - Currently not allowing 0-dim multi-tapes.

prop_Tt ix@Z = zs == ls where
  zs = id <<< T ... S.toList $ ix
  ls = [ Z ]
-}

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

{-
prop_TcMtTc ix@(Z:.Subword(i:.j)) = monadicIO $ do
  mxs :: PA.MutArr IO (PA.Unboxed (Z:.Subword) Int) <- run $ PA.fromListM (Z:.subword 0 0) (Z:.subword 0 100) [0 ..]
  let mt = MTbl (Z:.EmptyT) mxs :: MTbl (Z:.Subword) (PA.MutArr IO (PA.Unboxed (Z:.Subword) Int))
  zs <- run $ (,,) <<< (T:!chr xs) % mt % (T:!chr xs) ... SM.toList $ ix
  ls <- undefined -- run $ sequence $ [ (PA.readM mxs (Z:.subword (i+1) (j-1)) >>= \z -> return (Z:.xs VU.! i,z,Z:.xs VU.! (j-1))) | i>0, j<100, i+2<=j ]
  assert $ zs == ls
-}

{-
{-
-- | Our first multi-tape terminal ":-)"

-- | Increase dimension by 1. (1-tape grammars)

prop_P_Tt ix@(Z:.Point i) = zs == ls where
  zs = id <<< Term (T:.Chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! (i-1)) | i>0 ]
-}

-- | with peeking

{-
prop_P_CC ix@(Z:.Point i) = traceShow (zs,ls) $ zs == ls where
  zs = (,) <<< Chr xs % Chr xs ... S.toList $ ix
  ls = [ (xs VU.! (i-2), xs VU.! (i-1)) | i>1 ]
-}

prop_TcTc ix@(Z:.Point i) = {- traceShow (zs,ls) $ -} zs == ls where
  zs = (,) <<< Term (T:.Chr xs) % Term (T:.Chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! (i-2), Z:.xs VU.! (i-1)) | i>1 ]

-- deriving instance Show (Elm (None :. Term (T :. Chr Int)) (Z :. Point))

prop_TpTc ix@(Z:.Point i) = {- traceShow (zs,ls) $ -} zs == ls where
  zs = (,) <<< Term (T:.Peek (-1) xs) % Term (T:.Chr xs) ... S.toList $ ix
  ls = [ (Z:.f i, Z:.xs VU.! (i-1)) | i>0 ]
  f i = if i>1 then xs VU.! (i-2) else (-1)

prop_TcTpTc ix@(Z:.Point i) = {- traceShow (zs,ls) $ -} zs == ls where
  zs = (,,) <<< Term (T:.Chr xs) % Term (T:.Peek (-1) xs) % Term (T:.Chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! (i-2), Z:.f i, Z:.xs VU.! (i-1)) | i>1 ]
  f i = if i>1 then xs VU.! (i-2) else (-1)

{-
prop_Mt_Tc ix@(Z:.Subword(i:.j)) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Subword) Int) <- run $ PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ]
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % Term (T:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [(PA.readM mxs (Z:.subword i (j-1))) >>= \a -> return (a,Z:.xs VU.! (j-1)) | i<j ]
    assert $ zs == ls
-}

prop_P_Mt_Tt ix@(Z:.Point i) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Point) Int) <- run $ PA.fromListM (Z:.Point 0) (Z:.Point 100) [0 .. ]
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % Term (T:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [(PA.readM mxs (Z:.Point (i-1))) >>= \a -> return (a,Z:.xs VU.! (i-1)) | i>0 ]
    assert $ zs == ls

prop_P_Mt_TpTc ix@(Z:.Point i) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Point) Int) <- run $ PA.fromListM (Z:.Point 0) (Z:.Point 100) [0 .. ]
    let mt = mtable mxs
    let f i = if i>1 then xs VU.! (i-2) else (-1)
    zs <- run $ (,,) <<< mt % Term (T:.Peek (-1) xs) % Term (T:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [(PA.readM mxs (Z:.Point (i-1))) >>= \a -> return (a,Z:.f i,Z:.xs VU.! (i-1)) | i>0 ]
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

prop_P_Ttt ix@(Z:.Point i:.Point j) = zs == ls where
  zs = id <<< Term (T:.Chr xs:.Chr xs) ... S.toList $ ix
  ls = [ (Z:.xs VU.! (i-1):.xs VU.! (j-1)) | i>0, j>0 ]

prop_P_Mt_Ttt ix@(Z:.Point i:.Point j) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Point:.Point) Int) <- run $ PA.fromListM (Z:.Point 0:.Point 0) (Z:.Point 100:.Point 100) [0 .. ]
    let mt = mtable mxs
    zs <- run $ (,) <<< mt % Term (T:.Chr xs:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [(PA.readM mxs (Z:.Point (i-1):.Point (j-1))) >>= \a -> return (a,Z:.xs VU.! (i-1):.xs VU.! (j-1)) | i>0,j>0 ]
    assert $ zs == ls

prop_P_Mt_Tpp_Ttt ix@(Z:.Point i:.Point j) = monadicIO $ do
    mxs :: (PA.MU IO (Z:.Point:.Point) Int) <- run $ PA.fromListM (Z:.Point 0:.Point 0) (Z:.Point 100:.Point 100) [0 .. ]
    let mt = mtable mxs
    let f i j = Z:. (if i>1 then xs VU.! (i-2) else (-1)) :. (if j>1 then xs VU.! (j-2) else (-1))
    zs <- run $ (,,) <<< mt % Term (T:.Peek (-1) xs:.Peek (-1) xs) % Term (T:.Chr xs:.Chr xs) ... SM.toList $ ix
    ls <- run $ sequence $ [(PA.readM mxs (Z:.Point (i-1):.Point (j-1))) >>= \a -> return (a,f i j,Z:.xs VU.! (i-1):.xs VU.! (j-1)) | i>0,j>0 ]
    -- traceShow (zs,ls) $
    assert $ zs == ls

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

mtable xs = MTable Eall xs

{-
-- | A subword (i,j) should always produce an index in the allowed range

prop_subwordIndex (Small n, Subword (i:.j)) = (n>j) ==> p where
  p = n * (n+1) `div` 2 >= k
  k = subwordIndex (subword 0 n) (subword i j)
-}

-}

-- | data set. Can be made fixed as the maximal subword size is statically known!

xs = VU.fromList [0 .. 99 :: Int]


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


