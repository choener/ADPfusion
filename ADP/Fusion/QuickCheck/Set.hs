
{-# Options_GHC -O0 #-}

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
       , let kk = popShiftL ix (BitSet k)
       ]

prop_b_ii_nn ix@(BitSet _) = zs == ls where
  tia = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  tib = ITbl NonEmpty xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... S.toList) highestB ix
  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = popShiftL ix (BitSet k)
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
       , let kk = popShiftL ix          (BitSet k)
       , let ll = popShiftL (ix `xor` kk) (BitSet l)
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
       , let kk = popShiftL ix          (BitSet k)
       , let ll = popShiftL (ix `xor` kk) (BitSet l)
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

-- | Edges should never work as a single terminal element.

prop_bii_e :: BS2I First Last -> Bool
prop_bii_e ix@(s:>Iter i:>Iter j) = zs == ls where
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = (id <<< e ... S.toList) highestBII ix
  ls = [] :: [ (Int,Int) ]

-- | Edges extend only in cases where in @i -> j@, @i@ actually happens to
-- be a true interface.

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
       , popCount t >= 2
       , k <- activeBitsL t
       , k /= getIter i
       ]

prop_bii_iee :: BS2I First Last -> Bool
prop_bii_iee ix@(s:>i:>Iter j) = L.sort zs == L.sort ls where
  tia = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = ((,,) <<< tia % e % e ... S.toList) highestBII ix
  ls = [ ( xsBII ! (t:>i:>kk) , (k,l) , (l,j) )
       | let tmp = (s `clearBit` j)
       , l <- activeBitsL tmp
       , l /= getIter i
       , let t = tmp `clearBit` l
       , k <- activeBitsL t
       , let kk = Iter k
       ]

prop_bii_ieee :: BS2I First Last -> Bool
prop_bii_ieee ix@(s:>i:>Iter j) = L.sort zs == L.sort ls where
  tia = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = ((,,,) <<< tia % e % e % e ... S.toList) highestBII ix
  ls = [ ( xsBII ! (t:>i:>kk) , (k,l) , (l,m) , (m,j) )
       | let tmpM = (s `clearBit` j)
       , m <- activeBitsL tmpM
       , m /= getIter i
       , let tmpL = (tmpM `clearBit` m)
       , l <- activeBitsL tmpL
       , l /= getIter i
       , let t = tmpL `clearBit` l
       , k <- activeBitsL t
       , let kk = Iter k
       ]

prop_bii_iee_n :: BS2I First Last -> Bool
prop_bii_iee_n ix@(s:>i:>Iter j) = L.sort zs == L.sort ls where
  tia = ITbl NonEmpty xsBII (\ _ _ -> Id 1)
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = ((,,) <<< tia % e % e ... S.toList) highestBII ix
  ls = [ ( xsBII ! (t:>i:>kk) , (k,l) , (l,j) )
       | let tmp = (s `clearBit` j)
       , l <- activeBitsL tmp
       , l /= getIter i
       , let t = tmp `clearBit` l
       , popCount t >= 2
       , k <- activeBitsL t
       , k /= getIter i
       , let kk = Iter k
       ]

prop_bii_ieee_n :: BS2I First Last -> Bool
prop_bii_ieee_n ix@(s:>i:>Iter j) = L.sort zs == L.sort ls where
  tia = ITbl NonEmpty xsBII (\ _ _ -> Id 1)
  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
  zs = ((,,,) <<< tia % e % e % e ... S.toList) highestBII ix
  ls = [ ( xsBII ! (t:>i:>kk) , (k,l) , (l,m) , (m,j) )
       | let tmpM = (s `clearBit` j)
       , m <- activeBitsL tmpM
       , m /= getIter i
       , let tmpL = (tmpM `clearBit` m)
       , l <- activeBitsL tmpL
       , l /= getIter i
       , let t = tmpL `clearBit` l
       , popCount t >= 2
       , k <- activeBitsL t
       , k /= getIter i
       , let kk = Iter k
       ]

-- prop_bii_ii (ix@(s:>i:>j) :: (BitSet:>Interface First:>Interface Last)) = tr zs ls $ zs == ls where
--   tia = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
--   tib = ITbl EmptyOk xsBII (\ _ _ -> Id 1)
--   zs = ((,) <<< tia % tib ... S.toList) highestBII ix
--   ls = [ ( xsBII ! kk , xsBII ! ll )
--        | k  <- VU.toList . popCntSorted $ popCount s
--        , ki <- if k==0 then [0] else activeBitsL k
--        , kj <- if | k==0 -> [0] | popCount k==1 -> [ki] | otherwise -> activeBitsL (k `clearBit` ki)
--        , let kk = (BitSet k:>Iter ki:>Iter kj)
--        , let l  = s `xor` BitSet k
--        , li <- if l==0 then [0] else activeBitsL l
--        , lj <- if | l==0 -> [0] | popCount l==1 -> [li] | otherwise -> activeBitsL (l `clearBit` li)
--        , let ll = (l:>Iter li:>Iter lj)
--        ]



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

options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

