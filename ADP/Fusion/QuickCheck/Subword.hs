
{-# Options_GHC -O0 #-}

-- |
--
-- TODO need to carefully check all props against boundary errors!
-- Especially the 2-dim cases!

module ADP.Fusion.QuickCheck.Subword where

import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.List as L
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic

import           Data.PrimitiveArray

import           ADP.Fusion
import           ADP.Fusion.QuickCheck.Common



-- * Outside checks

-- ** two non-terminals on the r.h.s.
--
-- A_ij -> B_ik C_kj
--
-- B*_ik -> A*_ij C_kj
-- C*_kj -> B_ik  A*_ij

prop_sv_OI ox@(Subword (i:.k)) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,) <<< toa % tic ... stoList) maxSWo ox
  ls = [ ( unsafeIndex xoS (subword i j)
         , unsafeIndex xsS (subword k j) )
       | j <- [ k .. highest ] ]

prop_sv_IO ox@(Subword (k:.j)) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs = ((,) <<< tib % toa ... stoList) maxSWo ox
  ls = [ ( unsafeIndex xsS (subword i k)
         , unsafeIndex xoS (subword i j) )
       | j <= highest, i <- [ 0 .. k ] ]

-- ** three non-terminals on the r.h.s. (this provides situations where two
-- syntactic terminals are on the same side)
--
-- A_ij -> B_ik C_kl D_lj
--
-- B*_ik -> A*_ij C_kl  D_lj
-- C*_kl -> B_ik  A*_ij D_lj
-- D*_lj -> B_ik  C_kl  A*_ij

prop_sv_OII ox@(Subword (i:.k)) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  tid = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,,) <<< toa % tic % tid ... stoList) maxSWo ox
  ls = [ ( unsafeIndex xoS (subword i j)
         , unsafeIndex xsS (subword k l)
         , unsafeIndex xsS (subword l j) )
       | j <- [ k .. highest ], l <- [ k .. j ] ]

prop_sv_IOI ox@(Subword (k:.l)) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tid = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,,) <<< tib % toa % tid ... stoList) maxSWo ox
  ls = [ ( unsafeIndex xsS (subword i k)
         , unsafeIndex xoS (subword i j)
         , unsafeIndex xsS (subword l j) )
       | i <- [ 0 .. k ], j <- [ l .. highest ] ]

prop_sv_IIO ox@(Subword (l:.j)) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs = ((,,) <<< tib % tic % toa ... stoList) maxSWo ox
  ls = [ ( unsafeIndex xsS (subword i k)
         , unsafeIndex xsS (subword k l)
         , unsafeIndex xoS (subword i j) )
       | j <= highest, i <- [ 0 .. l ], k <- [ i .. l ] ]

-- ** four non-terminals on the r.h.s. ?

-- ** five non-terminals on the r.h.s. ?

-- ** Non-terminal and terminal combinations

prop_cOc ox@(Subword (i:.j)) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs  = ((,,) <<< chr csS % toa % chr csS ... stoList) maxSWo ox
  ls  = [ ( csS VU.! (i-1)
          , unsafeIndex xoS (subword (i-1) (j+1))
          , csS VU.! (j  ) )
        | i > 0 && j < highest ]

prop_ccOcc ox@(Subword (i:.j)) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs  = ((,,,,) <<< chr csS % chr csS % toa % chr csS % chr csS ... stoList) maxSWo ox
  ls  = [ ( csS VU.! (i-2)
          , csS VU.! (i-1)
          , unsafeIndex xoS (subword (i-2) (j+2))
          , csS VU.! (j  )
          , csS VU.! (j+1) )
        | i > 1 && j < highest -1 ]

prop_cOccc ox@(Subword (i:.j)) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs  = ((,,,,) <<< chr csS % toa % chr csS % chr csS % chr csS ... stoList) maxSWo ox
  ls  = [ ( csS VU.! (i-1)
          , unsafeIndex xoS (subword (i-1) (j+3))
          , csS VU.! (j  )
          , csS VU.! (j+1)
          , csS VU.! (j+2) )
        | i > 0 && j < highest -2 ]

-- ** Terminals, syntactic terminals, and non-terminals

prop_cOcIc ox@(Subword (i:.k)) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,,,,) <<< chr csS % toa % chr csS % tic % chr csS ... stoList) maxSWo ox
  ls = [ ( csS VU.! (i-1)
         , unsafeIndex xoS (subword (i-1)  j   )
         , csS VU.! (k  )
         , unsafeIndex xsS (subword (k+1) (j-1))
         , csS VU.! (j-1) )
       | i > 0, j <- [ k+2 .. highest ] ]

prop_cIcOc ox@(Subword (k:.j)) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs = ((,,,,) <<< chr csS % tib % chr csS % toa % chr csS ... stoList) maxSWo ox
  ls = [ ( csS VU.! (i  )
         , unsafeIndex xsS (subword (i+1) (k-1))
         , csS VU.! (k-1)
         , unsafeIndex xoS (subword  i    (j+1))
         , csS VU.! (j  ) )
       | j+1 <= highest, k>1, i <- [ 0 .. k-2 ] ]

-- ** Epsilonness

prop_Epsilon ox@(Subword (i:.j)) = zs == ls where
  zs = (id <<< Epsilon ... stoList) (maxSWo) ox
  ls = [ () | i==0 && j==highest ]


-- ** Multi-tape cases

prop_2dimIt ix@(Z:.Subword (i:.j):.Subword (k:.l)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsSS (\ _ _ -> Id ((1,1),(1,1)))
  zs = (id <<< t ... stoList) (Z:.subword 0 highest:.subword 0 highest) ix
  ls = [ ( unsafeIndex xsSS ix ) | j<=highest && l<=highest ]

{-
xprop_2dimItIt ix@(Z:.Subword (i:.j):.Subword (k:.l)) = zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsSS (\ _ _ -> Id (1,1))
  zs = ((,) <<< t % t ... stoList) (Z:.subword 0 highest:.subword 0 highest) ix
  ls = [ ( unsafeIndex xsSS (Z:.subword i m:.subword k n)
         , unsafeIndex xsSS (Z:.subword m j:.subword n l) )
       | j<=highest && l<=highest
       , m <- [i..j]
       , n <- [k..l]
       ]
-}

prop_2dimcIt ix@(Z:.Subword(i:.j):.Subword(k:.l)) = {- traceShow (zs,ls) $ -} zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsSS (\ _ _ -> Id ((1,1),(1,1)))
  zs = ((,) <<< (M:|chr csS:|chr csS) % t ... stoList) (Z:.subwordI 0 highest:.subwordI 0 highest) ix
  ls = [ ( Z :. (csS VU.! i) :. (csS VU.! k)
         , unsafeIndex xsSS (Z :. subword (i+1) j :. subword (k+1) l) )
       | j<=highest && l<=highest
       , i+1<=j && k+1<=l ]

prop_2dimItc ix@(Z:.Subword(i:.j):.Subword(k:.l)) = {- traceShow (zs,ls) $ -} zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsSS (\ _ _ -> Id ((1,1),(1,1)))
  zs = ((,) <<< t % (M:|chr csS:|chr csS)  ... stoList) (Z:.subwordI 0 highest:.subwordI 0 highest) ix
  ls = [ ( unsafeIndex xsSS (Z :. subword i (j-1) :. subword k (l-1))
         , Z :. (csS VU.! (j-1)) :. (csS VU.! (l-1)) )
       | j<=highest && l<=highest
       , i+1<=j && k+1<=l ]

prop_2dimcItc ix@(Z:.Subword(i:.j):.Subword(k:.l)) = {- traceShow (zs,ls) $ -} zs == ls where
  t = ITbl 0 0 (Z:.EmptyOk:.EmptyOk) xsSS (\ _ _ -> Id ((1,1),(1,1)))
  zs = ((,,) <<< (M:|chr csS:|chr csS) % t % (M:|chr csS:| chr csS) ... stoList) (Z:.subwordI 0 highest:.subwordI 0 highest) ix
  ls = [ ( Z :. (csS VU.! i) :. (csS VU.! k)
         , unsafeIndex xsSS (Z :. subword (i+1) (j-1) :. subword (k+1) (l-1))
         , Z :. (csS VU.! (j-1)) :. (csS VU.! (l-1)) )
       | j<=highest && l<=highest
       , i+2<=j && k+2<=l ]



stoList = unId . SM.toList

highest = 3 -- 10

maxSWi :: Subword I
maxSWi = subword 0 highest

maxSWo :: Subword O
maxSWo = subword 0 highest

csS :: VU.Vector (Int,Int)
csS = VU.fromList [ (i,i+1) | i <- [0 .. highest-1] ] -- this should be @highest -1@, we should die if we see @(highest,highest+1)@

xsS :: Unboxed (Subword I) (Int,Int)
xsS = fromList (subword 0 0) (subword 0 highest) [ (i,j) | i <- [ 0 .. highest ] , j <- [ i .. highest ] ]

xoS :: Unboxed (Subword O) (Int,Int)
xoS = fromList (subword 0 0) (subword 0 highest) [ (i,j) | i <- [ 0 .. highest ] , j <- [ i .. highest ] ]

xsSS :: Unboxed (Z:.Subword I:.Subword I) ( (Int,Int) , (Int,Int) )
xsSS = fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 highest:.subword 0 highest) ((-1,-1),(-1,-1))
        $ Prelude.map (\((i,j),(k,l)) -> (Z:.subword i j:.subword k l, ((i,j),(k,l)) )) [ ((i,j) , (k,l)) | i <- [0 .. highest], j <-[i .. highest], k <- [0 .. highest], l <- [0 .. highest] ]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 10000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

