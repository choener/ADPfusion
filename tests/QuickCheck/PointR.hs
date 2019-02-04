
{-# Options_GHC -O0 #-}

module QuickCheck.PointR where

import           Control.Applicative
import           Control.Monad
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util
import           Debug.Trace
--import           GHC.TypeNats
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.IO.Unsafe
import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic
#ifdef ADPFUSION_TEST_SUITE_PROPERTIES
import           Test.Tasty.TH
import           Test.Tasty.QuickCheck
#endif

import           Data.PrimitiveArray

import           ADP.Fusion.PointR



-- * Epsilon cases

prop_I_Epsilon ix@(PointR j) = zs == ls where
  zs = (id <<< Epsilon ... stoList) maxPRi ix
  ls = [ () | j == getLtPr maxPRi ]

prop_I_ZEpsilon ix@(Z:.PointR j) = zs == ls where
  zs = (id <<< (M:|Epsilon) ... stoList) (ZZ:..maxPRi) ix
  ls = [ Z:.() | j == getLtPr maxPRi ]



-- * Deletion cases

--prop_I_ItNC ix@(PointR j) = zs == ls where
--  zs = ((,,) <<< tSI % Deletion % chr xs ... stoList) maxPRi ix
--  ls = [ ( unsafeIndex xsP (PointR $ j-1)
--         , ()
--         , xs VU.! (j-1)
--         ) | j >= 1, j <= (maxI) ]
--
--prop_I_2dimIt_NC_CN ix@(Z:.PointR j:.PointR l) = zs == ls where
--  zs = ((,,) <<< tZ2I % (M:|Deletion:|chr xs) % (M:|chr xs:|Deletion) ... stoList) (ZZ:..maxPRi:..maxPRi) ix
--  ls = [ ( unsafeIndex xsPP (Z:.PointR (j-1):.PointR (l-1))
--         , Z:.()           :.xs VU.! (l-1)
--         , Z:.xs VU.! (j-1):.()
--         ) | j>=1, l>=1, j<=maxI, l<=maxI ]



-- * terminal cases

-- | A single character terminal
--
-- X_j -> c_j || j==1

prop_I_Tt ix@(Z:.PointR j) = zs == ls where
  zs = (id <<< (M:|chr xs) ... stoList) (ZZ:..maxPRi) ix
  ls = [ (Z:.xs VU.! j) | j==arbMaxPointR-1 ]

-- | Two single-character terminals

prop_I_CC ix@(Z:.PointR i) = zs == ls where
  zs = ((,) <<< (M:|chr xs) % (M:|chr xs) ... stoList) (ZZ:..maxPRi) ix
  ls = [ (Z:.xs VU.! (i+0), Z:.xs VU.! (i+1)) | i==arbMaxPointR-2 ]

-- | Just a table

prop_I_It ix@(PointR j) = zs == ls where
  zs = (id <<< tSI ... stoList) maxPRi ix
  ls = [ unsafeIndex xsP ix | j>=0, j<=arbMaxPointR ]

prop_I_ZIt ix@(Z:.PointR j) = zs == ls where
  zs = (id <<< tZ1I ... stoList) (ZZ:..maxPRi) ix
  ls = [ unsafeIndex xsZP ix | j>=0, j<=arbMaxPointR ]

prop_I_2dimIt ix@(Z:.PointR i:.PointR j) = zs == ls where
  zs = (id <<< tZ2I ... stoList) (ZZ:..maxPRi:..maxPRi) ix
  ls = [ unsafeIndex xsPP ix | j>=0, j<=arbMaxPointR ]

-- | single terminal followed by table

prop_I_ItC ix@(PointR j) = zs == ls where
  zs = ((,) <<< chr xs % tSI ... stoList) maxPRi ix
  ls = [ ( xs VU.! j
         , unsafeIndex xsP (PointR $ j+1)
         ) | j>=0, j+1<=arbMaxPointR ]

-- | synvar followed by a 2-tape character terminal

prop_I_2dimItCC ix@(Z:.PointR j:.PointR l) = zs == ls where
  zs = ((,,) <<< (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) % tZ2I ... stoList) (ZZ:..maxPRi:..maxPRi) ix
  ls = [ ( Z:.xs VU.! (j+0):.xs VU.! (l+0)
         , Z:.xs VU.! (j+1):.xs VU.! (l+1)
         , unsafeIndex xsPP (Z:.PointR (j+2):.PointR (l+2))
         ) | j>=0, l>=0, j+2<=arbMaxPointR, l+2<=arbMaxPointR ]



stoList = unId . SM.toList

--infixl 8 >>>
--(>>>) f xs = \lu ij -> SM.map f . mkStream (build xs) (initialContext ij) lu $ ij

tSI  = TW (ITbl @_ @_ @_ @_ @0 @0 EmptyOk xsP)  (\ (_ :: LimitType (PointR I)) (_ :: PointR I) -> Id (1::Int))
tZ1I = TW (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk) xsZP) (\ (_::LimitType (Z:.PointR I)) (_::Z:.PointR I) -> Id (1::Int))
tZ2I = TW (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk:.EmptyOk) xsPP) (\ (_::LimitType (Z:.PointR I:.PointR I)) (_::Z:.PointR I:.PointR I) -> Id (1::Int))

xsP :: Unboxed (PointR I) Int
xsP = fromList maxPRi [0 ..]

xsZP :: Unboxed (Z:.PointR I) Int
xsZP = fromList (ZZ:..maxPRi) [0 ..]

xsPP :: Unboxed (Z:.PointR I:.PointR I) Int
xsPP = fromList (ZZ:..maxPRi:..maxPRi) [0 ..]

mxsPP = unsafePerformIO $ zzz where
  zzz :: IO (MutArr IO (Unboxed (Z:.PointR I:.PointR I) Int))
  zzz = fromListM (ZZ:..maxPRi:..maxPRi) [0 ..]

maxPRi :: LimitType (PointR I)
maxPRi = LtPointR arbMaxPointR

xs = VU.fromList [0 .. arbMaxPointR - 1 :: Int]

getLtPr (LtPointR k) = k

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000 } -- 0}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck



#ifdef ADPFUSION_TEST_SUITE_PROPERTIES
testgroup_point = $(testGroupGenerator)
#endif

