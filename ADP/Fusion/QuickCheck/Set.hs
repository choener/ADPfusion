
{-# Language TemplateHaskell #-}

module ADP.Fusion.QuickCheck.Set where

import           Data.Bits
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.List as L
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Unboxed as VU
import           Test.QuickCheck
import           Test.QuickCheck.All
import           Test.QuickCheck.Monadic

import           Data.Bits.Ordered
import           Data.PrimitiveArray

import           ADP.Fusion
import           ADP.Fusion.QuickCheck.Common



-- * Inside checks

prop_ii ix@(BitSet _) = zs == ls where
  tia = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  tib = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... S.toList) highest ix
  ls = [ ( xsS ! kk , xsS ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = movePopulation ix (BitSet k)
       ]

prop_iii ix@(BitSet _) = zs == ls where
  tia = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  tib = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  tic = ITbl EmptyOk xsS (\ _ _ -> Id 1)
  zs = ((,,) <<< tia % tib % tic ... S.toList) highest ix
  ls = [ ( xsS ! kk , xsS ! ll , xsS ! mm )
       | k <- VU.toList . popCntSorted $ popCount ix
       , l <- VU.toList . popCntSorted $ popCount ix - popCount k
       , let kk = movePopulation ix          (BitSet k)
       , let ll = movePopulation (ix `xor` kk) (BitSet l)
       , let mm = (ix `xor` (kk .|. ll))
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
  ls = [ ( unsafeIndex xoS (O $ BitSet undefined)
         , undefined
         )
       | undefined ]
-}

-- * Complement checks

-- | An inside and an outside symbol together yield the universe.

{-
prop_c_OI x@(C (BitSet s)) = zs == ls where
  zs = undefined
  ls = [ ( unsafeIndex xoS (O $ BitSet s)
         , unsafeIndex xsS (    BitSet s)
         )
       | highest == s .|. (s `xor` highest) -- obviously
       -- TODO rewrite the line above in terms of elements, not indices?
       ]
-}

-- * Helper functions

highBit = arbitraryBitSetMax -- should be the same as the highest bit in Index.Set.arbitrary
highest = BitSet $ 2^(highBit+1) -1

xsS :: Unboxed BitSet Int
xsS = fromList (BitSet 0) highest [ 0 .. ]

xoS :: Unboxed (Outside BitSet) Int
xoS = fromList (O (BitSet 0)) (O highest) [ 0 .. ]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 10000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck

