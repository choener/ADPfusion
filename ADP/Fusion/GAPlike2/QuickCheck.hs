{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}

module ADP.Fusion.GAPlike2.QuickCheck where

import Test.QuickCheck
import Test.QuickCheck.All
import qualified Data.Vector.Fusion.Stream as SP
import qualified Data.Vector.Unboxed as VU

import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import Data.PrimitiveArray

import ADP.Fusion.QuickCheck.Arbitrary
import ADP.Fusion.GAPlike2.Common
import ADP.Fusion.GAPlike2



-- * QuickCheck

checkC_fusion (i,j) = id <<< Chr dvu ... SP.toList $ (i,j)
checkC_list   (i,j) = [dvu VU.! i | i+1==j]
prop_checkC = checkC_fusion === checkC_list

checkCC_fusion (i,j) = (,) <<< Chr dvu % Chr dvu ... SP.toList $ (i,j)
checkCC_list   (i,j) = [ (dvu VU.! i, dvu VU.! (i+1)) | i+2==j ]
prop_checkCC = checkCC_fusion === checkCC_list

checkP_fusion (i,j) = id <<< (Tbl pat :: Tbl E PAT)  ... SP.toList $ (i,j)
checkP_list   (i,j) = [ (pat!(Z:.i:.j)) | i<=j ]
prop_checkP = checkP_fusion === checkP_list

checkPP_fusion (i,j) = let tbl = Tbl pat :: Tbl E PAT
                       in  (,) <<< tbl % tbl ... SP.toList $ (i,j)
checkPP_list   (i,j) = [ (pat!(Z:.i:.k), pat!(Z:.k:.j)) | k<-[i..j] ]
prop_checkPP = checkPP_fusion === checkPP_list

checkCPC_fusion (i,j) = let tbl = Tbl pat :: Tbl E PAT
                        in  (,,) <<< Chr dvu % tbl % Chr dvu ... SP.toList $ (i,j)
checkCPC_list (i,j) = [ (dvu VU.! i, pat!(Z:.i+1:.j-1), dvu VU.! (j-1)) | i+2<=j ]
prop_checkCPC = checkCPC_fusion === checkCPC_list

checkNN_fusion (i,j) = let tbl = Tbl pat :: Tbl N PAT
                       in  (,) <<< tbl % tbl ... SP.toList $ (i,j)
checkNN_list   (i,j) = [ (pat!(Z:.i:.k), pat!(Z:.k:.j)) | k<-[i+1..j-1] ]
prop_checkNN = checkNN_fusion === checkNN_list



options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

allProps = $forAllProperties customCheck

