
{-# Options_GHC -O0 #-}

{-# Language TemplateHaskell #-}
{-# Language TypeOperators #-}

module ADP.Fusion.QuickCheck.Point where

import           Control.Applicative
import           Control.Monad
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.IO.Unsafe
import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic

import           Data.PrimitiveArray

import ADP.Fusion



-- * Epsilon cases

prop_Epsilon ix@(PointL j) = zs == ls where
  zs = (id <<< Epsilon ... S.toList) (PointL 100) ix
  ls = [ () | j == 0 ]

prop_O_Epsilon ix@(O (PointL j)) = zs == ls where
  zs = (id <<< Epsilon ... S.toList) (O (PointL 100)) ix
  ls = [ () | j == 100 ]

prop_ZEpsilon ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< (M:|Epsilon) ... S.toList) (Z:.PointL 100) ix
  ls = [ Z:.() | j == 0 ]

prop_O_ZEpsilon ix@(O (Z:.PointL j)) = zs == ls where
  zs = (id <<< (M:|Epsilon) ... S.toList) (O (Z:.PointL 100)) ix
  ls = [ Z:.() | j == 100 ]

prop_O_ZEpsilonEpsilon ix@(O (Z:.PointL j:.PointL l)) = zs == ls where
  zs = (id <<< (M:|Epsilon:|Epsilon) ... S.toList) (O (Z:.PointL 100:.PointL 100)) ix
  ls = [ Z:.():.() | j == 100, l == 100 ]



-- * Deletion cases

prop_O_ItNC ix@(O (PointL j)) = zs == ls where
  t = ITbl 0 0 EmptyOk xsPo (\ _ _ -> Id 1)
  zs = ((,,) <<< t % Deletion % chr xs ... S.toList) (O $ PointL 100) ix
  ls = [ ( unsafeIndex xsPo (O $ PointL $ j+1)
         , ()
         , xs VU.! (j+0)
         ) | j >= 0, j <= 99 ]
{-# Noinline prop_O_ItNC #-}

prop_O_ZItNC ix@(O (Z:.PointL j)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk) xsZPo (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|Deletion) % (M:|chr xs) ... S.toList) (O (Z:.PointL 100)) ix
  ls = [ ( unsafeIndex xsZPo (O (Z:.PointL (j+1)))
         , Z:.()
         , Z:.xs VU.! (j+0)
         ) | j >= 0, j <= 99 ]

prop_O_2dimIt_NC_CN ix@(O (Z:.PointL j:.PointL l)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsPPo (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|Deletion:|chr xs) % (M:|chr xs:|Deletion) ... S.toList) (O (Z:.PointL 100:.PointL 100)) ix
  ls = [ ( unsafeIndex xsPPo (O (Z:.PointL (j+1):.PointL (l+1)))
         , Z:.()           :.xs VU.! (l+0)
         , Z:.xs VU.! (j+0):.()
         ) | j>=0, l>=0, j<=99, l<=99 ]

prop_2dimIt_NC_CN ix@(Z:.PointL j:.PointL l) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsPP (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|Deletion:|chr xs) % (M:|chr xs:|Deletion) ... S.toList) (Z:.PointL 100:.PointL 100) ix
  ls = [ ( unsafeIndex xsPP (Z:.PointL (j-1):.PointL (l-1))
         , Z:.()           :.xs VU.! (l-1)
         , Z:.xs VU.! (j-1):.()
         ) | j>=1, l>=1, j<=100, l<=100 ]



-- * terminal cases

-- | A single character terminal

prop_Tt ix@(Z:.PointL j) = zs == ls where
  zs = (id <<< (M:|chr xs) ... S.toList) (Z:.PointL 100) ix
  ls = [ (Z:.xs VU.! (j-1)) | 1==j ]

--prop_O_Tt ix@(Z:.O (PointL j)) = traceShow (j,zs,ls) $ zs == ls where
--  zs = (id <<< (M:|chr xs) ... S.toList) (Z:.O (PointL 100)) ix
--  ls = [ (Z:.xs VU.! (j-1)) | 1==j ]

-- | Two single-character terminals

prop_CC ix@(Z:.PointL i) = zs == ls where
  zs = ((,) <<< (M:|chr xs) % (M:|chr xs) ... S.toList) (Z:.PointL 100) ix
  ls = [ (Z:.xs VU.! (i-2), Z:.xs VU.! (i-1)) | 2==i ]

-- | Just a table

prop_It ix@(PointL j) = zs == ls where
  t = ITbl 0 0 EmptyOk xsP (\ _ _ -> Id 1)
  zs = (id <<< t ... S.toList) (PointL 100) ix
  ls = [ unsafeIndex xsP ix | j>=0, j<=100 ]

prop_O_It ix@(O (PointL j)) = zs == ls where
  t = ITbl 0 0 EmptyOk xsPo (\ _ _ -> Id 1)
  zs = (id <<< t ... S.toList) (O (PointL 100)) ix
  ls = [ unsafeIndex xsPo ix | j>=0, j<=100 ]

prop_ZIt ix@(Z:.PointL j) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk) xsZP (\ _ _ -> Id 1)
  zs = (id <<< t ... S.toList) (Z:.PointL 100) ix
  ls = [ unsafeIndex xsZP ix | j>=0, j<=100 ]

prop_O_ZIt ix@(O (Z:.PointL j)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk) xsZPo (\ _ _ -> Id 1)
  zs = (id <<< t ... S.toList) (O (Z:.PointL 100)) ix
  ls = [ unsafeIndex xsZPo ix | j>=0, j<=100 ]

-- | Table, then single terminal

prop_ItC ix@(PointL j) = zs == ls where
  t = ITbl 0 0 EmptyOk xsP (\ _ _ -> Id 1)
  zs = ((,) <<< t % chr xs ... S.toList) (PointL 100) ix
  ls = [ ( unsafeIndex xsP (PointL $ j-1)
         , xs VU.! (j-1)
         ) | j>=1, j<=100 ]

-- | @A^*_j -> A^*_{j+1} c_{j+1)@ !

prop_O_ItC ix@(O (PointL j)) = zs == ls where
  t = ITbl 0 0 EmptyOk xsPo (\ _ _ -> Id 1)
  zs = ((,) <<< t % chr xs ... S.toList) (O $ PointL 100) ix
  ls = [ ( unsafeIndex xsPo (O $ PointL $ j+1)
         , xs VU.! (j+0)
         ) | j >= 0, j < 100 ]

prop_O_ItCC ix@(O (PointL j)) = zs == ls where
  t = ITbl 0 0 EmptyOk xsPo (\ _ _ -> Id 1)
  zs = ((,,) <<< t % chr xs % chr xs ... S.toList) (O $ PointL 100) ix
  ls = [ ( unsafeIndex xsPo (O $ PointL $ j+2)
         , xs VU.! (j+0)
         , xs VU.! (j+1)
         ) | j >= 0, j <= 98 ]
{-# Noinline prop_O_ItCC #-}

prop_O_ZItCC ix@(O (Z:.PointL j)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk) xsZPo (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|chr xs) % (M:|chr xs) ... S.toList) (O (Z:.PointL 100)) ix
  ls = [ ( unsafeIndex xsZPo (O (Z:.PointL (j+2)))
         , Z:.xs VU.! (j+0)
         , Z:.xs VU.! (j+1)
         ) | j >= 0, j <= 98 ]

-- | synvar followed by a 2-tape character terminal

prop_2dimItCC ix@(Z:.PointL j:.PointL l) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsPP (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) ... S.toList) (Z:.PointL 100:.PointL 100) ix
  ls = [ ( unsafeIndex xsPP (Z:.PointL (j-2):.PointL (l-2))
         , Z:.xs VU.! (j-2):.xs VU.! (l-2)
         , Z:.xs VU.! (j-1):.xs VU.! (l-1)
         ) | j>=2, l>=2, j<=100, l<=100 ]

prop_O_2dimItCC ix@(O (Z:.PointL j:.PointL l)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsPPo (\ _ _ -> Id 1)
  zs = ((,,) <<< t % (M:|chr xs:|chr xs) % (M:|chr xs:|chr xs) ... S.toList) (O (Z:.PointL 100:.PointL 100)) ix
  ls = [ ( unsafeIndex xsPPo (O (Z:.PointL (j+2):.PointL (l+2)))
         , Z:.xs VU.! (j+0):.xs VU.! (l+0)
         , Z:.xs VU.! (j+1):.xs VU.! (l+1)
         ) | j>=0, l>=0, j<=98, l<=98 ]

-- * direct index tests

xprop_O_ixZItCC ix@(O (Z:.PointL j)) = zs where
  t = ITbl 0 0 (Z:.EmptyOk) xsZPo (\ _ _ -> Id 1)
  zs = (id >>> t % (M:|chr xs) % (M:|chr xs) ... S.toList) (O (Z:.PointL 100)) ix

infixl 8 >>>
(>>>) f xs = \lu ij -> S.map f . mkStream (build xs) (initialContext ij) lu $ ij

class GetIxs x i where
  type R x i :: *
  getIxs :: Elm x i -> R x i

instance GetIxs S i where
  type R S i = Z:.(i,i)
  getIxs e = Z:.(getIdx e, getOmx e)

instance GetIxs ls i => GetIxs (ls :!: Chr a b) i where
  type R (ls :!: Chr a b) i = R ls i :. (i,i)
  getIxs (ElmChr _ i o s) = getIxs s :. (i,o)

instance GetIxs ls i => GetIxs (ls :!: ITbl m a i x) i where
  type R (ls :!: ITbl m a i x) i = R ls i :. (i,i)
  getIxs (ElmITbl _ i o s) = getIxs s :. (i,o)

xsP :: Unboxed (PointL) Int
xsP = fromList (PointL 0) (PointL 100) [0 ..]

xsZP :: Unboxed (Z:.PointL) Int
xsZP = fromList (Z:.PointL 0) (Z:.PointL 100) [0 ..]

xsPo :: Unboxed (Outside (PointL)) Int
xsPo = fromList (O $ PointL 0) (O $ PointL 100) [0 ..]

xsZPo :: Unboxed (Outside (Z:.PointL)) Int
xsZPo = fromList (O (Z:.PointL 0)) (O (Z:.PointL 100)) [0 ..]

xsPP :: Unboxed (Z:.PointL:.PointL) Int
xsPP = fromList (Z:.PointL 0:.PointL 0) (Z:.PointL 100:.PointL 100) [0 ..]

xsPPo :: Unboxed (Outside (Z:.PointL:.PointL)) Int
xsPPo = fromList (O (Z:.PointL 0:.PointL 0)) (O (Z:.PointL 100:.PointL 100)) [0 ..]

mxsPP = unsafePerformIO $ zzz where
  zzz :: IO (MutArr IO (Unboxed (Z:.PointL:.PointL) Int))
  zzz = fromListM (Z:.PointL 0:.PointL 0) (Z:.PointL 100:.PointL 100) [0 ..]

xs = VU.fromList [0 .. 99 :: Int]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

