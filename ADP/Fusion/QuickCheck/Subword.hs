
{-# Options_GHC -O0 #-}

{-# Language TemplateHaskell #-}

module ADP.Fusion.QuickCheck.Subword where

import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic
import qualified Data.Vector.Fusion.Stream as S
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.List as L
import qualified Data.Vector.Unboxed as VU

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

prop_sv_OI ox@(O (Subword (i:.k))) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,) <<< toa % tic ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( unsafeIndex xoS (O $ subword i j)
         , unsafeIndex xsS (    subword k j) )
       | j <- [ k .. highest ] ]

prop_sv_IO ox@(O (Subword (k:.j))) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs = ((,) <<< tib % toa ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( unsafeIndex xsS (    subword i k)
         , unsafeIndex xoS (O $ subword i j) )
       | j <= highest, i <- [ 0 .. k ] ]

-- ** three non-terminals on the r.h.s. (this provides situations where two
-- syntactic terminals are on the same side)
--
-- A_ij -> B_ik C_kl D_lj
--
-- B*_ik -> A*_ij C_kl  D_lj
-- C*_kl -> B_ik  A*_ij D_lj
-- D*_lj -> B_ik  C_kl  A*_ij

prop_sv_OII ox@(O (Subword (i:.k))) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  tid = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,,) <<< toa % tic % tid ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( unsafeIndex xoS (O $ subword i j)
         , unsafeIndex xsS (    subword k l)
         , unsafeIndex xsS (    subword l j) )
       | j <- [ k .. highest ], l <- [ k .. j ] ]

prop_sv_IOI ox@(O (Subword (k:.l))) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tid = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,,) <<< tib % toa % tid ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( unsafeIndex xsS (    subword i k)
         , unsafeIndex xoS (O $ subword i j)
         , unsafeIndex xsS (    subword l j) )
       | i <- [ 0 .. k ], j <- [ l .. highest ] ]

prop_sv_IIO ox@(O (Subword (l:.j))) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs = ((,,) <<< tib % tic % toa ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( unsafeIndex xsS (    subword i k)
         , unsafeIndex xsS (    subword k l)
         , unsafeIndex xoS (O $ subword i j) )
       | j <= highest, i <- [ 0 .. l ], k <- [ i .. l ] ]

-- ** four non-terminals on the r.h.s. ?

-- ** five non-terminals on the r.h.s. ?

-- ** Non-terminal and terminal combinations

prop_cOc ox@(O( Subword (i:.j))) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs  = ((,,) <<< chr csS % toa % chr csS ... S.toList) (O $ subword 0 highest) ox
  ls  = [ ( csS VU.! (i-1)
          , unsafeIndex xoS (O $ subword (i-1) (j+1))
          , csS VU.! (j  ) )
        | i > 0 && j < highest ]

prop_ccOcc ox@(O(Subword (i:.j))) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs  = ((,,,,) <<< chr csS % chr csS % toa % chr csS % chr csS ... S.toList) (O $ subword 0 highest) ox
  ls  = [ ( csS VU.! (i-2)
          , csS VU.! (i-1)
          , unsafeIndex xoS (O $ subword (i-2) (j+2))
          , csS VU.! (j  )
          , csS VU.! (j+1) )
        | i > 1 && j < highest -1 ]

prop_cOccc ox@(O(Subword (i:.j))) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs  = ((,,,,) <<< chr csS % toa % chr csS % chr csS % chr csS ... S.toList) (O $ subword 0 highest) ox
  ls  = [ ( csS VU.! (i-1)
          , unsafeIndex xoS (O $ subword (i-1) (j+3))
          , csS VU.! (j  )
          , csS VU.! (j+1)
          , csS VU.! (j+2) )
        | i > 0 && j < highest -2 ]

-- ** Terminals, syntactic terminals, and non-terminals

prop_cOcIc ox@(O (Subword (i:.k))) = zs == ls where
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  tic = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  zs = ((,,,,) <<< chr csS % toa % chr csS % tic % chr csS ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( csS VU.! (i-1)
         , unsafeIndex xoS (O $ subword (i-1)  j    )
         , csS VU.! (k  )
         , unsafeIndex xsS (    subword (k+1) (j-1) )
         , csS VU.! (j-1) )
       | i > 0, j <- [ k+2 .. highest ] ]

prop_cIcOc ox@(O (Subword (k:.j))) = zs == ls where
  tib = ITbl 0 0 EmptyOk xsS (\ _ _ -> Id (1,1))
  toa = ITbl 0 0 EmptyOk xoS (\ _ _ -> Id (1,1))
  zs = ((,,,,) <<< chr csS % tib % chr csS % toa % chr csS ... S.toList) (O $ subword 0 highest) ox
  ls = [ ( csS VU.! (i  )
         , unsafeIndex xsS (    subword (i+1) (k-1))
         , csS VU.! (k-1)
         , unsafeIndex xoS (O $ subword  i    (j+1))
         , csS VU.! (j  ) )
       | j+1 <= highest, k>1, i <- [ 0 .. k-2 ] ]

-- ** Emptyness

prop_Empty ox@(O (Subword (i:.j))) = zs == ls where
  zs = (id <<< Empty ... S.toList) (O $ subword 0 highest) ox
  ls = [ () | i==0 && j==highest ]



highest = 2

csS :: VU.Vector (Int,Int)
csS = VU.fromList [ (i,i+1) | i <- [0 .. highest] ] -- this should be @highest -1@, we should die if we see @(highest,highest+1)@

xsS :: Unboxed Subword (Int,Int)
xsS = fromList (subword 0 0) (subword 0 highest) [ (i,j) | i <- [ 0 .. highest ] , j <- [ i .. highest ] ]

xoS :: Unboxed (Outside Subword) (Int,Int)
xoS = fromList (O $ subword 0 0) (O $ subword 0 highest) [ (i,j) | i <- [ 0 .. highest ] , j <- [ i .. highest ] ]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 10000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

