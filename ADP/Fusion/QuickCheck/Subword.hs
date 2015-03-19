
{-# Language TemplateHaskell #-}

module ADP.Fusion.QuickCheck.Subword where

import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic
import qualified Data.Vector.Fusion.Stream as S
import           Data.Vector.Fusion.Util

import           Data.PrimitiveArray

import           ADP.Fusion



-- * Outside checks

-- ** two non-terminals on the r.h.s.
--
-- A_ij -> B_ik C_kj
--
-- B*_ik -> A*_ij C_kj
-- C*_kj -> B_ik  A*_ij

prop_sv_OI ox@(O (Subword (i:.k))) = zs == ls where
  toa = ITbl EmptyOk xoS (\ _ _ -> Id 1)
  tic = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  zs = ((,) <<< toa % tic ... S.toList) (O $ subword 0 100) ox
  ls = [ ( unsafeIndex xoS (O $ subword i j)
         , unsafeIndex xsS (    subword k j) )
       | j <- [ k .. 100 ] ]

prop_sv_IO ox@(O (Subword (k:.j))) = zs == ls where
  tib = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  toa = ITbl EmptyOk xoS (\ _ _ -> Id 1)
  zs = ((,) <<< tib % toa ... S.toList) (O $ subword 0 100) ox
  ls = [ ( unsafeIndex xsS (    subword i k)
         , unsafeIndex xoS (O $ subword i j) )
       | i <- [ 0 .. k ] ]

-- ** three non-terminals on the r.h.s. (this provides situations where two
-- syntactic terminals are on the same side)
--
-- A_ij -> B_ik C_kl D_lj
--
-- B*_ik -> A*_ij C_kl  D_lj
-- C*_kl -> B_ik  A*_ij D_lj
-- D*_lj -> B_ik  C_kl  A*_ij

prop_sv_OII ox@(O (Subword (i:.k))) = zs == ls where
  toa = ITbl EmptyOk xoS (\ _ _ -> Id 1)
  tic = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  tid = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  zs = ((,,) <<< toa % tic % tid ... S.toList) (O $ subword 0 100) ox
  ls = [ ( unsafeIndex xoS (O $ subword i j)
         , unsafeIndex xsS (    subword k l)
         , unsafeIndex xsS (    subword l j) )
       | l <- [ k .. 100 ], j <- [ l .. 100 ] ]

prop_sv_IOI ox@(O (Subword (k:.l))) = zs == ls where
  tib = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  toa = ITbl EmptyOk xoS (\ _ _ -> Id 1)
  tid = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  zs = ((,,) <<< tib % toa % tid ... S.toList) (O $ subword 0 100) ox
  ls = [ ( unsafeIndex xsS (    subword i k)
         , unsafeIndex xoS (O $ subword k l)
         , unsafeIndex xsS (    subword l j) )
       | i <- [ 0 .. k ], j <- [ l .. 100 ] ]

prop_sv_IIO ox@(O (Subword (l:.j))) = zs == ls where
  tib = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  tic = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  toa = ITbl EmptyOk xoS (\ _ _ -> Id 1)
  zs = ((,,) <<< tib % tic % toa ... S.toList) (O $ subword 0 100) ox
  ls = [ ( unsafeIndex xsS (    subword i k)
         , unsafeIndex xsS (    subword k l)
         , unsafeIndex xoS (O $ subword i j) )
       | i <- [ 0 .. l ], k <- [ i .. l ] ]

-- ** four non-terminals on the r.h.s. ?

-- ** five non-terminals on the r.h.s. ?

xsS :: Unboxed Subword Int
xsS = fromList (subword 0 0) (subword 0 100) [ 1 .. ]

xoS :: Unboxed (Outside Subword) Int
xoS = fromList (O $ subword 0 0) (O $ subword 0 100) [ 1 .. ]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

