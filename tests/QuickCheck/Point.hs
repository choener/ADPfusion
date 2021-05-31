
{-# Options_GHC -O0 #-}

module QuickCheck.Point where

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
-- #ifdef ADPFUSION_TEST_SUITE_PROPERTIES
import           Test.Tasty.TH
import           Test.Tasty.QuickCheck
-- #endif

import           Data.PrimitiveArray

import           ADPfusion.PointL



-- * Epsilon cases

prop_I_Epsilon ix@(PointL j) = zs == ls where
  zs = (id <<< Epsilon @Global ... stoList) maxPLi ix
  ls = [ () | j == 0 ]

prop_O_Epsilon ix@(PointL j) = zs == ls where
  zs = (id <<< Epsilon @Global ... stoList) maxPLo ix
  ls = [ () | j == maxI ]

prop_I_ZEpsilon ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< (M:|Epsilon @Global) ... stoList) (ZZ:..maxPLi) ix
  ls = [ Z:.() | j == 0 ]

prop_O_ZEpsilon ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< (M:|Epsilon @Global) ... stoList) (ZZ:..maxPLo) ix
  ls = [ Z:.() | j == maxI ]

prop_O_ZEpsilonEpsilon ix@(Z:.PointL j:.PointL l) = zs == ls where
  zs = (id <<< (M:|Epsilon @Global:|Epsilon @Global) ... stoList) (ZZ:..maxPLo:..maxPLo) ix
  ls = [ Z:.():.() | j == maxI, l == maxI ]



-- * Deletion cases

prop_I_ItNC ix@(PointL j) = zs == ls where
  zs = ((,,) <<< tSI % Deletion % chr xs ... stoList) maxPLi ix
  ls = [ ( unsafeIndex xsP (PointL $ j-1)
         , ()
         , xs VU.! (j-1)
         ) | j >= 1, j <= (maxI) ]

prop_O_ItNC ix@(PointL j) = zs == ls where
  zs = ((,,) <<< tSO % Deletion % chr xs ... stoList) maxPLo ix
  ls = [ ( unsafeIndex xsPo (PointL $ j+1)
         , ()
         , xs VU.! (j+0)
         ) | j >= 0, j <= (maxI-1) ]
{-# Noinline prop_O_ItNC #-}

prop_O_ZItNC ix@(Z:.PointL j) = zs == ls where
  zs = ((,,) <<< tZ1O % (M:|Deletion) % (M:|chr xs) ... stoList) (ZZ:..maxPLo) ix
  ls = [ ( unsafeIndex xsZPo (Z:.PointL (j+1))
         , Z:.()
         , Z:.xs VU.! (j+0)
         ) | j >= 0, j <= (maxI-1) ]

prop_O_2dimIt_NC_CN ix@(Z:.PointL j:.PointL l) = zs == ls where
  zs = ((,,) <<< tZ2O % (M:|Deletion:|chr xs) % (M:|chr xs:|Deletion) ... stoList) (ZZ:..maxPLo:..maxPLo) ix
  ls = [ ( unsafeIndex xsPPo (Z:.PointL (j+1):.PointL (l+1))
         , Z:.()           :.xs VU.! (l+0)
         , Z:.xs VU.! (j+0):.()
         ) | j>=0, l>=0, j<=(maxI-1), l<=(maxI-1) ]

prop_I_2dimIt_NC_CN ix@(Z:.PointL j:.PointL l) = zs == ls where
  zs = ((,,) <<< tZ2I % (M:|Deletion:|chr xs) % (M:|chr xs:|Deletion) ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ ( unsafeIndex xsPP (Z:.PointL (j-1):.PointL (l-1))
         , Z:.()           :.xs VU.! (l-1)
         , Z:.xs VU.! (j-1):.()
         ) | j>=1, l>=1, j<=maxI, l<=maxI ]



-- * terminal cases

-- | A single character terminal
--
-- X_j -> c_j || j==1

prop_I_Tt ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< (M:|chr xs) ... stoList) (ZZ:..maxPLi) ix
  ls = [ (Z:.xs VU.! (j-1)) | 1==j ]

-- |
--
-- X_j     -> ε_{j-1} c_j   ||| j==1
-- E_{j-1} -> X_{j}   c_j
-- E_j     -> X_{j+1} c_{j+1}    ||| j-1==max ?!

prop_O_Tt ix@(Z:.(PointL j))
  | zs == ls  = True
  | otherwise = traceShow (j,zs,ls) False
  where
    zs = (id <<< (M:|chr xs) ... stoList) (ZZ:..maxPLo) ix
    ls = [ (Z:.xs VU.! j) | j==maxI-1 ]

-- | Two single-character terminals

prop_I_CC ix@(Z:.PointL i) = zs == ls where
  zs = ((,) <<< (M:|chr xs) % (M:|chr xs) ... stoList) (ZZ:..maxPLi) ix
  ls = [ (Z:.xs VU.! (i-2), Z:.xs VU.! (i-1)) | 2==i ]

-- | Just a table

prop_I_It ix@(PointL j) = zs == ls where
  zs = (id <<< tSI ... stoList) maxPLi ix
  ls = [ unsafeIndex xsP ix | j>=0, j<=maxI ]

prop_O_It ix@(PointL j) = zs == ls where
  zs = (id <<< tSO ... stoList) maxPLo ix
  ls = [ unsafeIndex xsPo ix | j>=0, j<=maxI ]

prop_I_ZIt ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< tZ1I ... stoList) (ZZ:..maxPLi) ix
  ls = [ unsafeIndex xsZP ix | j>=0, j<=maxI ]

prop_I_2dimIt ix@(Z:.PointL i:.PointL j) = zs == ls where
  zs = (id <<< tZ2I ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ unsafeIndex xsPP ix | j>=0, j<=maxI ]

prop_O_ZIt ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< tZ1O ... stoList) (ZZ:..maxPLo) ix
  ls = [ unsafeIndex xsZPo ix | j>=0, j<=maxI ]

-- | Table, then single terminal

prop_I_ItC ix@(PointL j) = zs == ls where
  zs = ((,) <<< tSI % chr xs ... stoList) maxPLi ix
  ls = [ ( unsafeIndex xsP (PointL $ j-1)
         , xs VU.! (j-1)
         ) | j>=1, j<=maxI ]

-- | @A^*_j -> A^*_{j+1} c_{j+1)@ !

prop_O_ItC ix@(PointL j)
  | zs == ls  = True
  | otherwise = traceShow (j,zs,ls) False
  where
    zs = ((,) <<< tSO % chr xs ... stoList) maxPLo ix
    ls = [ ( unsafeIndex xsPo (PointL $ j+1)
           , xs VU.! (j+0)  -- j-1 in inside, here moved one right!
           ) | j >= 0, j <= (maxI-1) ]

prop_O_ItCC ix@(PointL j) = zs == ls where
  zs = ((,,) <<< tSO % chr xs % chr xs ... stoList) maxPLo ix
  ls = [ ( unsafeIndex xsPo (PointL $ j+2)
         , xs VU.! (j+0)
         , xs VU.! (j+1)
         ) | j >= 0, j <= (maxI-2) ]

prop_O_ItCCC ix@(PointL j) = zs == ls where
  zs = ((,,,) <<< tSO % chr xs % chr xs % chr xs ... stoList) maxPLo ix
  ls = [ ( unsafeIndex xsPo (PointL $ j+3)
         , xs VU.! (j+0)
         , xs VU.! (j+1)
         , xs VU.! (j+2)
         ) | j >= 0, j <= (maxI-3) ]

prop_O_ZItCC ix@(Z:.PointL j) = zs == ls where
  zs = ((,,) <<< tZ1O % (M:|chr xs) % (M:|chr xs) ... stoList) (ZZ:..maxPLo) ix
  ls = [ ( unsafeIndex xsZPo (Z:.PointL (j+2))
         , Z:.xs VU.! (j+0)
         , Z:.xs VU.! (j+1)
         ) | j >= 0, j <= (maxI-2) ]

-- | synvar followed by a 2-tape character terminal

prop_I_2dimItCC ix@(Z:.PointL j:.PointL l) = zs == ls where
  zs = ((,,) <<< tZ2I % (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ ( unsafeIndex xsPP (Z:.PointL (j-2):.PointL (l-2))
         , Z:.xs VU.! (j-2):.xs VU.! (l-2)
         , Z:.xs VU.! (j-1):.xs VU.! (l-1)
         ) | j>=2, l>=2, j<=maxI, l<=maxI ]

prop_O_2dimItCC ix@(Z:.PointL j:.PointL l) = zs == ls where
  zs = ((,,) <<< tZ2O % (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) ... stoList) (ZZ:..maxPLo:..maxPLo) ix
  ls = [ ( unsafeIndex xsPPo (Z:.PointL (j+2):.PointL (l+2))
         , Z:.xs VU.! (j+0):.xs VU.! (l+0)
         , Z:.xs VU.! (j+1):.xs VU.! (l+1)
         ) | j>=0, l>=0, j<=(maxI-2), l<=(maxI-2) ]

-- * 'Strng' tests

-- ** Just the 'Strng' terminal

prop_I_ManyV ix@(PointL j) = zs == ls where
  zs = (id <<< manyV xs ... stoList) maxPLi ix
  ls = [ (VU.slice 0 j xs) ]

prop_I_SomeV ix@(PointL j)
  | zs == ls  = True
  | otherwise = traceShow (ix,zs,ls) False
  where
  zs = (id <<< someV xs ... stoList) maxPLi ix
  ls = [ (VU.slice 0 j xs) | j>0 ]

prop_2dim_ManyV_ManyV ix@(Z:.PointL i:.PointL j) = zs == ls where
  zs = (id <<< (M:|manyV xs:|manyV xs) ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ (Z:.VU.slice 0 i xs:.VU.slice 0 j xs) ]

prop_2dim_SomeV_SomeV ix@(Z:.PointL i:.PointL j) = zs == ls where
  zs = (id <<< (M:|someV xs:|someV xs) ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ (Z:.VU.slice 0 i xs:.VU.slice 0 j xs) | i > 0 && j > 0 ]

-- ** Together with a syntactic variable.

prop_I_Itbl_ManyV ix@(PointL i) = zs == ls where
  zs = ((,) <<< tSI % manyV xs ... stoList) maxPLi ix
  ls = [ (unsafeIndex xsP (PointL k), VU.slice k (i-k) xs) | k <- [0..i] ]

prop_I_Itbl_SomeV ix@(PointL i) = zs == ls where
  zs = ((,) <<< tSI % someV xs ... stoList) maxPLi ix
  ls = [ (unsafeIndex xsP (PointL k), VU.slice k (i-k) xs) | k <- [0..i-1] ]

-- | NOTE Be aware of the needed match between the type-level and value-level
-- @13@s.

prop_I_Itbl_Str ix@(PointL i) = zs == ls where
  zs = ((,) <<< tSI % str @_ @_ @"" @13 @Nothing xs ... stoList) maxPLi ix
  ls = [ (unsafeIndex xsP (PointL k), VU.slice k (i-k) xs) | k <- [0..i-13] ]

-- | And now for some funny type-level shenanigans.

prop_I_Itbl_StrTyLvl (Positive bound', ix@(PointL i)) = let bound = bound' `mod` 23 in
  case (someNatVal bound) of
    Nothing → error "zzz"
    Just (SomeNat (Proxy ∷ Proxy b)) →
      let zs = ((,) <<< tSI % str @_ @_ @"" @b @Nothing xs ... stoList) maxPLi ix
          ls = [ (unsafeIndex xsP (PointL k), VU.slice k (i-k) xs) | k <- [0..i-bv] ]
          bv = fromIntegral $ natVal (Proxy ∷ Proxy b)
      in  zs == ls

prop_I_1dim_Itbl_ManyV ix@(Z:.PointL i) = zs == ls where
  zs = ((,) <<< tZ1I % (M:|manyV xs) ... stoList) (ZZ:..maxPLi) ix
  ls = [ (unsafeIndex xsZP (Z:.PointL k), Z:. VU.slice k (i-k) xs) | k <- [0..i] ]

prop_I_1dim_Itbl_SomeV ix@(Z:.PointL i) = zs == ls where
  zs = ((,) <<< tZ1I % (M:|someV xs) ... stoList) (ZZ:..maxPLi) ix
  ls = [ (unsafeIndex xsZP (Z:.PointL k), Z:. VU.slice k (i-k) xs) | k <- [0..i-1] ]

prop_I_2dim_Itbl_ManyV_ManyV ix@(Z:.PointL i:.PointL j) = zs == ls where
  zs = ((,) <<< tZ2I % (M:|manyV xs:|manyV xs) ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ (unsafeIndex xsPP (Z:.PointL k:.PointL l), Z:. VU.slice k (i-k) xs :. VU.slice l (j-l) xs) | k <- [0..i], l <- [0..j] ]

prop_I_2dim_Itbl_SomeV_SomeV ix@(Z:.PointL i:.PointL j) = zs == ls where
  zs = ((,) <<< tZ2I % (M:|someV xs:|someV xs) ... stoList) (ZZ:..maxPLi:..maxPLi) ix
  ls = [ (unsafeIndex xsPP (Z:.PointL k:.PointL l), Z:. VU.slice k (i-k) xs :. VU.slice l (j-l) xs) | k <- [0..i-1], l <- [0..j-1] ]



stoList = unId . SM.toList

--infixl 8 >>>
--(>>>) f xs = \lu ij -> SM.map f . mkStream (build xs) (initialContext ij) lu $ ij

tSI  = TW (ITbl @_ @_ @_ @_ @0 @0 EmptyOk xsP)  (\ (_ :: LimitType (PointL I)) (_ :: PointL I) -> Id (1::Int))
tSO  = TW (ITbl @_ @_ @_ @_ @0 @0 EmptyOk xsPo) (\ (_ :: LimitType (PointL O)) (_ :: PointL O) -> Id (1::Int))
tZ1I = TW (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk) xsZP) (\ (_::LimitType (Z:.PointL I)) (_::Z:.PointL I) -> Id (1::Int))
tZ1O = TW (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk) xsZPo) (\ (_::LimitType (Z:.PointL O)) (_::Z:.PointL O) -> Id (1::Int))
tZ2I = TW (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk:.EmptyOk) xsPP) (\ (_::LimitType (Z:.PointL I:.PointL I)) (_::Z:.PointL I:.PointL I) -> Id (1::Int))
tZ2O = TW (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk:.EmptyOk) xsPPo) (\ (_::LimitType (Z:.PointL O:.PointL O)) (_::Z:.PointL O:.PointL O) -> Id (1::Int))

xsP :: Unboxed (PointL I) Int
xsP = fromList maxPLi [0 ..]

xsZP :: Unboxed (Z:.PointL I) Int
xsZP = fromList (ZZ:..maxPLi) [0 ..]

xsPo :: Unboxed (PointL O) Int
xsPo = fromList maxPLo [0 ..]

xsZPo :: Unboxed (Z:.PointL O) Int
xsZPo = fromList (ZZ:..maxPLo) [0 ..]

xsPP :: Unboxed (Z:.PointL I:.PointL I) Int
xsPP = fromList (ZZ:..maxPLi:..maxPLi) [0 ..]

xsPPo :: Unboxed (Z:.PointL O:.PointL O) Int
xsPPo = fromList (ZZ:..maxPLo:..maxPLo) [0 ..]

mxsPP = unsafePerformIO $ zzz where
  zzz :: IO (MutArr IO (Unboxed (Z:.PointL I:.PointL I) Int))
  zzz = fromListM (ZZ:..maxPLi:..maxPLi) [0 ..]

maxI =100

maxPLi :: LimitType (PointL I)
maxPLi = LtPointL maxI

maxPLo :: LimitType (PointL O)
maxPLo = LtPointL maxI

xs = VU.fromList [0 .. maxI - 1 :: Int]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000 } -- 0}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck



-- #ifdef ADPFUSION_TEST_SUITE_PROPERTIES
testgroup_point = $(testGroupGenerator)
-- #endif

