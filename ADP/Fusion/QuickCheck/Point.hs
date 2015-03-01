
{-# Language TypeOperators #-}

module ADP.Fusion.QuickCheck.Point where

import           Control.Applicative
import           Control.Monad
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.IO.Unsafe
import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic
import           Data.Vector.Fusion.Util

import           Data.PrimitiveArray

import ADP.Fusion



-- | A single character terminal

prop_Tt ix@(Z:.PointL i) = zs == ls where
  zs = (id <<< (M:|chr xs) ... S.toList) (Z:.PointL 100) ix
  ls = [ (Z:.xs VU.! (i-1)) | 1==i ]

-- | Two single-character terminals

prop_CC ix@(Z:.PointL i) = zs == ls where
  zs = ((,) <<< (M:|chr xs) % (M:|chr xs) ... S.toList) (Z:.PointL 100) ix
  ls = [ (Z:.xs VU.! (i-2), Z:.xs VU.! (i-1)) | 2==i ]

-- | Just a table

prop_It ix@(PointL i) = zs == ls where
  t = ITbl EmptyOk xsP (\ _ _ -> Id 1)
  zs = (id <<< t ... S.toList) (PointL 100) ix
  ls = [ unsafeIndex xsP ix | i>=0, i<=100 ]

-- | Table, then single terminal

prop_ItC ix@(PointL i) = zs == ls where
  t = ITbl EmptyOk xsP (\ _ _ -> Id 1)
  zs = ((,) <<< t % chr xs ... S.toList) (PointL 100) ix
  ls = [ ( unsafeIndex xsP (PointL $ i-1)
         , xs VU.! (i-1)
         ) | i>=1, i<=100 ]

-- | synvar followed by a 2-tape character terminal

prop_2dimItCC ix@(Z:.PointL j:.PointL l) = zs == ls where
  t = ITbl (Z:.EmptyOk:.EmptyOk) xsPP (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) ... S.toList) (Z:.PointL 100:.PointL 100) ix
  ls = [ ( unsafeIndex xsPP (Z:.PointL (j-2):.PointL (l-2))
         , Z:.xs VU.! (j-2):.xs VU.! (l-2)
         , Z:.xs VU.! (j-1):.xs VU.! (l-1)
         ) | j>=2, l>=2, j<=100, l<=100 ]

{-
-- | left-linear outside grammar

prop_O_It ix@(O (PointL(i:.j))) = zs == ls where
  t = ITbl EmptyOk xsPo (\ _ _ -> Id 1)
  zs = (id <<< t ... S.toList) (O $ pointL 0 0) ix
  ls = [ unsafeIndex xsPo (O $ pointL i j) | j-i>=0, i==0, j<=100 ]

-- | left-linear outside grammar

prop_O_ItC ix@(O (PointL(i:.j))) = zs == ls where
  t = ITbl EmptyOk xsPo (\ _ _ -> Id 1)
  zs = ((,) <<< t % chr xs ... S.toList) (O $ pointL 0 0) ix
  ls = [ ( unsafeIndex xsPo (O $ pointL i (j-1))
         , xs VU.! (j-1)
         ) | j-i>=1, i==0, j<=100 ]
-}

{-
prop_P_2dimMtCC ix@(Z:.PointL(i:.j):.PointL(k:.l)) = monadicIO $ do
  mxs <- run $ pure $ mxsPP
  let mt = ITbl (Z:.EmptyOk:.EmptyOk) mxs (const $ return undefined)
  zs <- run $ (((,,) <<< mt % (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) ... SM.toList) (Z:.PointL (0:.0):.(PointL (0:.0)))) (Z:.PointL (0:.0):.PointL (0:.0)) ix
  ls <- run $ sequence $ [ liftM3 (,,)   (readM mxs (Z:.pointL i (j-2):.pointL k (l-2)))
                                         (pure $ Z:.xs VU.! (j-2):.xs VU.! (l-2))
                                         (pure $ Z:.xs VU.! (j-1):.xs VU.! (l-1))
                         | j-i>=2, l-k>=2, i==0, j<=100, k==0, l<=100] --, a<-[i+1..j-2], b<-[k+1..l-2] ]
  if zs==ls
    then assert $ zs==ls
    else traceShow (zs,ls) $ assert False
-}

xsP :: Unboxed (PointL) Int
xsP = fromList (PointL 0) (PointL 100) [0 ..]

xsPo :: Unboxed (Outside (PointL)) Int
xsPo = fromList (O $ PointL 0) (O $ PointL 100) [0 ..]

xsPP :: Unboxed (Z:.PointL:.PointL) Int
xsPP = fromList (Z:.PointL 0:.PointL 0) (Z:.PointL 100:.PointL 100) [0 ..]

mxsPP = unsafePerformIO $ zzz where
  zzz :: IO (MutArr IO (Unboxed (Z:.PointL:.PointL) Int))
  zzz = fromListM (Z:.PointL 0:.PointL 0) (Z:.PointL 100:.PointL 100) [0 ..]

xs = VU.fromList [0 .. 99 :: Int]

