
{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
{-# Language MultiWayIf #-}

module ADP.Fusion.QuickCheck.Set where

import           Data.Bits
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.List as L
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Unboxed as VU
import           Test.QuickCheck hiding (NonEmpty)
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic

import           Data.Bits.Ordered
import           Data.PrimitiveArray

import           ADP.Fusion
import           ADP.Fusion.QuickCheck.Common



-- * BitSets without interfaces

-- ** Inside checks

prop_b_ii ix@(BitSet _) = zs == ls where
  tia = ITbl EmptyOk xsB (\ _ _ -> Id 1)
  tib = ITbl EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... S.toList) highestB ix
  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = movePopulation ix (BitSet k)
       ]

prop_b_ii_nn ix@(BitSet _) = zs == ls where
  tia = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  tib = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... S.toList) highestB ix
  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = movePopulation ix (BitSet k)
       , popCount kk > 0
       , popCount (ix `xor` kk) > 0
       ]

prop_b_iii ix@(BitSet _) = zs == ls where
  tia = ITbl EmptyOk xsB (\ _ _ -> Id 1)
  tib = ITbl EmptyOk xsB (\ _ _ -> Id 1)
  tic = ITbl EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,,) <<< tia % tib % tic ... S.toList) highestB ix
  ls = [ ( xsB ! kk , xsB ! ll , xsB ! mm )
       | k <- VU.toList . popCntSorted $ popCount ix
       , l <- VU.toList . popCntSorted $ popCount ix - popCount k
       , let kk = movePopulation ix          (BitSet k)
       , let ll = movePopulation (ix `xor` kk) (BitSet l)
       , let mm = (ix `xor` (kk .|. ll))
       ]

prop_b_iii_nnn ix@(BitSet _) = zs == ls where
  tia = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  tib = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  tic = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  zs = ((,,) <<< tia % tib % tic ... S.toList) highestB ix
  ls = [ ( xsB ! kk , xsB ! ll , xsB ! mm )
       | k <- VU.toList . popCntSorted $ popCount ix
       , l <- VU.toList . popCntSorted $ popCount ix - popCount k
       , let kk = movePopulation ix          (BitSet k)
       , let ll = movePopulation (ix `xor` kk) (BitSet l)
       , let mm = (ix `xor` (kk .|. ll))
       , popCount kk > 0, popCount ll > 0, popCount mm > 0
       ]


-- * Outside checks
-- These checks are very similar to those in the @Subword@ module. We just
-- need to be a bit more careful, as indexed sets have overlap.

-- ** Two non-terminals.
--
-- @A_s -> B_(s\t) C_t    (s\t) ++ t == s@
-- @s = 111 , s\t = 101, t = 010@
--
-- with @Z@ the full set.
-- @Z = 1111@

-- @B*_Z\(s\t) -> A*_Z\s C_t@
-- @Z\(s\t) = 1010, Z\s = 1000, t = 010@

{-
prop_OI ox@(O (BitSet _)) = ls where
  zs = undefined
  ls = [ ( unsafeIndex xoB (O $ BitSet undefined)
         , undefined
         )
       | undefined ]
-}

-- * Complement checks

-- | An inside and an outside symbol together yield the universe.

{-
prop_c_OI x@(C (BitSet s)) = zs == ls where
  zs = undefined
  ls = [ ( unsafeIndex xoB (O $ BitSet s)
         , unsafeIndex xsB (    BitSet s)
         )
       | highestB == s .|. (s `xor` highestB) -- obviously
       -- TODO rewrite the line above in terms of elements, not indices?
       ]
-}



-- * BitSets with two interfaces

-- ** Inside checks

prop_bii_i :: BS2I First Last -> Bool
prop_bii_i ix@(s:>i:>j) = zs == ls where
  tia = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
  zs = (id <<< tia ... S.toList) highestBII ix
  ls = [ xsBII ! ix ]

prop_bii_i_n :: BS2I First Last -> Bool
prop_bii_i_n ix@(s:>i:>j) = zs == ls where
  tia = ITbl NonEmpty xsBII (\ _ _ -> Id 1)
  zs = (id <<< tia ... S.toList) highestBII ix
  ls = [ xsBII ! ix | popCount s > 0 ]

prop_bii_ie :: BS2I First Last -> Bool
prop_bii_ie ix@(s:>i:>Iter j) = zs == ls where
  tia = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = ((,) <<< tia % e ... S.toList) highestBII ix
  ls = [ ( xsBII ! (t:>i:>(Iter k :: Interface Last)) , (k,j) )
       | let t = s `clearBit` j
       , k <- activeBitsL t ]

prop_bii_ie_n :: BS2I First Last -> Bool
prop_bii_ie_n ix@(s:>i:>Iter j) = zs == ls where
  tia = ITbl NonEmpty xsBII (\ _ _ -> Id 1)
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = ((,) <<< tia % e ... S.toList) highestBII ix
  ls = [ ( xsBII ! (t:>i:>(Iter k :: Interface Last)) , (k,j) )
       | let t = s `clearBit` j
       , popCount t > 0
       , k <- activeBitsL t ]

prop_bii_ii (ix@(s:>i:>j) :: (BitSet:>Interface First:>Interface Last)) = tr zs ls $ zs == ls where
  tia = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
  tib = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... S.toList) highestBII ix
  ls = [ ( xsBII ! kk , xsBII ! ll )
       | k  <- VU.toList . popCntSorted $ popCount s
       , ki <- if k==0 then [0] else activeBitsL k
       , kj <- if | k==0 -> [0] | popCount k==1 -> [ki] | otherwise -> activeBitsL (k `clearBit` ki)
       , let kk = (BitSet k:>Iter ki:>Iter kj)
       , let l  = s `xor` BitSet k
       , li <- if l==0 then [0] else activeBitsL l
       , lj <- if | l==0 -> [0] | popCount l==1 -> [li] | otherwise -> activeBitsL (l `clearBit` li)
       , let ll = (l:>Iter li:>Iter lj)
       ]



-- * Helper functions

highBit = fromIntegral arbitraryBitSetMax -- should be the same as the highest bit in Index.Set.arbitrary
highestB = BitSet $ 2^(highBit+1) -1
highestBII = highestB :> Iter (highBit-1) :> Iter (highBit-1) -- assuming @highBit >= 1@

xsB :: Unboxed BitSet Int
xsB = fromList (BitSet 0) highestB [ 0 .. ]

xoB :: Unboxed (Outside BitSet) Int
xoB = fromList (O (BitSet 0)) (O highestB) [ 0 .. ]

xsBII :: Unboxed (BitSet:>Interface First:>Interface Last) Int
xsBII = fromList (BitSet 0:>Iter 0:>Iter 0) highestBII [ 0 .. ]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 10000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

