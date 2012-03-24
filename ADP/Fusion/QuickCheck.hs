{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}

-- | QuickCheck properties for a number of ADPfusion combinators. Each test is
-- once written using ADPfusion and once using list comprehensions. Typing
-- @allProps@ in ghci will run all tests, prefixed @prop_@ with a thousand
-- tests each.

module ADP.Fusion.QuickCheck where

import Data.List
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Unboxed as VU
import Test.QuickCheck
import Test.QuickCheck.All

import "PrimitiveArray" Data.Array.Repa.Index

import ADP.Fusion.QuickCheck.Arbitrary
import qualified ADP.Fusion as F
import qualified ADP.Fusion.Monadic as M
import qualified ADP.Fusion.Monadic.Internal as F



options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

allProps = $forAllProperties customCheck



-- * Some definitions:
--
-- @O@ means one
-- @M@ means many
-- @P@ means one or more
-- @ML_x_y@ is for a makeLeftCombinator with boundaries x and y

-- ** @xs -~+ ys@, size @xs@ = 1, size @ys@ >= 1.

fOP (i,j) = S.toList $ (,) F.<<< fRegion F.-~+ fRegion F.... id $ Z:.i:.j

lOP (i,j) = [ ((i,i+1), (i+1,j)) | i+1<=j-1 ]

prop_OP = fOP === lOP

-- ** @xs -~~ ys -~~ zs@, size @xs@ = 1, size @ys@ = 1, size @zs@ >= 0.

fOOP (i,j) = S.toList $ (,,) F.<<< fRegion F.-~~ fRegion F.-~~ fRegion F.... id $ Z:.i:.j

lOOP (i,j) = [ ( (i,i+1), (i+1,i+2), (i+2,j) ) | i+2<=j ]

prop_OOP = fOOP === lOOP

-- ** @xs +~- ys@, size @xs@ >= 1, size @ys@ = 1.

fPO (i,j) = S.toList $ (,) F.<<< fRegion F.+~- fRegion F.... id $ Z:.i:.j

lPO (i,j) = [ ( (i,j-1), (j-1,j) ) | i+1<=j-1 ]

prop_PO (Small i, Small j) = fPO (i,j) == lPO (i,j)

-- ** @xs -~+ ys +~- zs@, size @xs@ = 1, size @ys@ >= 1, size @zs@ = 1. This is
-- a "hairpin" in RNA bioinformatics.

fOPO (i,j) = S.toList $ (,,) F.<<< fRegion F.-~+ fRegion F.+~- fRegion F.... id $ Z:.i:.j

lOPO (i,j) = [ ( (i,i+1), (i+1,j-1), (j-1,j) ) | i+2<=j, i+1<j-1 ]

prop_OPO = fOPO === lOPO

-- ** The central region is non-empty, with two size-1 regions on each side.
-- Will create @O(n)@ candidates, which will all fail, except for the last one
-- (if @j-i@ is large enough).

fOOPOOslow (i,j) = S.toList $ (,,,,) F.<<< fRegion F.-~+ fRegion F.-~+ fRegion F.+~+ fRegion F.-~- fRegion F.... id $ Z:.i:.j

lOOPOO (i,j) = [ ( (i,i+1), (i+1,i+2), (i+2,j-2), (j-2,j-1), (j-1,j) ) | i+4<=j, i+2<j-2 ]

prop_OOPOOslow = fOOPOOslow === lOOPOO

-- ** The above test can be sped up by the use of the @+~--@ combinator. It
-- fixes the left and right side, by allowing only exactly size two on its
-- right. Each combinator here will 'Yield' exactly once, then be 'Done'.

fOOPOOfast (i,j) = S.toList $ (,,,,) F.<<< fRegion F.-~+ fRegion F.-~+ fRegion F.+~-- fRegion F.-~- fRegion F.... id $ Z:.i:.j

prop_OOPOOfast = fOOPOOfast === lOOPOO

-- ** A complex right-hand side which was problematic in 0.0.0.3 of ADPfusion.
-- In original ADP @base -~~ weak ~~- base +~+ string@ we want the @base@ parts
-- to have size 1, @weak@ of any size, and @string@ to be non-empty. In
-- ADPfusion @as -~+ bs@ means that @as@ has size one, @bs@ size 1 or more.

fOPOP (i,j) = S.toList $ (,,,) F.<<< fRegion F.-~+ fRegion F.+~+ fRegion F.-~+ fRegion F.... id $ Z:.i:.j

lOPOP (i,j) = [ ( (i,i+1), (i+1,k), (k,k+1), (k+1,j) ) | k <- [i+1 .. j-2], i+1<k, k+1<j ]

prop_OPOP = fOPOP === lOPOP

-- ** One more of those complex right-hand sides. This one is already rather
-- complicated. We have @one -~+ one -~+ many +~+ one -~~ one -~+ plus@ where
-- @one@ has size 1, many has size 0 to many, plus has size 1 to many. The last
-- combinator @-~+@ again short-curcuits by being 'Done' once the left-hand
-- side is larger than one.

fOOPOOP (i,j) = S.toList $ (,,,,,) F.<<< fRegion F.-~+ fRegion F.-~+ fRegion F.+~+ fRegion F.-~~ fRegion F.-~+ fRegion F.... id $ Z:.i:.j

lOOPOOP (i,j) = [ ( (i,i+1), (i+1,i+2), (i+2,k), (k,k+1), (k+1,k+2), (k+2,j) ) | k <- [i+2 .. j-3], i+2<k, k+2<j ]

prop_OOPOOP = fOOPOOP === lOOPOOP

-- ** We now introduce two independently moving indices and size zero regions.

fMMM (i,j) = S.toList $ (,,) F.<<< fRegion F.~~~ fRegion F.~~~ fRegion F.... id $ Z:.i:.j

lMMM (i,j) = [ ( (i,k), (k,l), (l,j) ) | k <- [i..j], l<-[k..j] ]

prop_MMM = fMMM === lMMM

-- ** Three independent regions, each one enclosed by two size-1 regions.
-- Compile-time hog.

fOPOOPOOPO (i,j) = S.toList $ (,,,,,,,,) F.<<< fRegion F.-~+ fRegion F.+~+ fRegion F.-~+
                                          {--} fRegion F.-~+ fRegion F.+~+ fRegion F.-~+
                                          {--} fRegion F.-~+ fRegion F.+~- fRegion F.... id $ Z:.i:.j

lOPOOPOOPO (i,j) = [ ( (i,i+1), (i+1,k), (k,k+1), {--} (k+1,k+2), (k+2,l), (l,l+1), {--} (l+1,l+2), (l+2,j-1), (j-1,j) )
                   | k<-[i+1 .. j-5], l<-[k+2 .. j-3], i+1<k, k+2<l, l+2<j-1 ]

prop_OPOOPOOPO = fOPOOPOOPO === lOPOOPOOPO

-- ** Two non-empty regions, the right one with single-size regions around it.
-- (sorry about the name)

fPOPO (i,j) = S.toList $ (,,,) F.<<< fRegion F.+~+ fRegion F.-~+ fRegion F.+~- fRegion F.... id $ Z:.i:.j

lPOPO (i,j) = [ ( (i,k), (k,k+1), (k+1,j-1), (j-1,j) ) | k <- [i+1 .. j-3] ]

prop_POPO (Small i, Small j) = fPOPO (i,j) == lPOPO (i,j)

-- ** Sanity-checking special constraints.

fOO (i,j) = S.toList $ (,) F.<<< fRegion F.-~- fRegion F.... id $ Z:.i:.j

lOO (i,j) = [ ( (i,i+1), (j-1,j) ) | i+2==j ]

prop_OO (Small i, Small j) = fOO (i,j) == lOO (i,j)

-- ** Two non-empty regions

fPP (i,j) = S.toList $ (,) F.<<< fRegion F.+~+ fRegion F.... id $ Z:.i:.j

lPP (i,j) = [ ( (i,k), (k,j) ) | k<-[i+1 .. j-1] ]

prop_PP (Small i, Small j) = fPP (i,j) == lPP (i,j)

-- ** using 'makeLeft_MinRight'

fML_1_4M (i,j) = S.toList $ (,) F.<<< fRegion `ml_1_4` fRegion F.... id $ Z:.i:.j where
  infixl 9 `ml_1_4`
  ml_1_4 = F.makeLeft_MinRight (1,4) 0

lML_1_4M (i,j) = [ ( (i,k), (k,j) ) | k <- [i+1 .. min (i+4) j] ]

prop_ML_1_4M = fML_1_4M === lML_1_4M

-- ** using 'makeLeft_MinRight' and 'makeMinLeft_Right'. Inner regions fixed to
-- be non-empty.

fML_1_4MMR_1_4 (i,j) = S.toList $ (,,) F.<<< fRegion `ml_1_4` fRegion `mr_1_4` fRegion F.... id $ Z:.i:.j where
  infixl 9 `ml_1_4`
  ml_1_4 = F.makeLeft_MinRight (1,4) 1
  infixl 9 `mr_1_4`
  mr_1_4 = F.makeMinLeft_Right 1 (1,4)

lML_1_4MMR_1_4 (i,j) = [ ( (i,k), (k,l), (l,j) ) | k<-[i+1 .. min (i+4) j], l <- [max k (j-4) .. j-1], k<l ]

prop_ML_1_4MMR_1_4 = fML_1_4MMR_1_4 === lML_1_4MMR_1_4

