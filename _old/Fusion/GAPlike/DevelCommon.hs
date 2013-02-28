{-# LANGUAGE PackageImports #-}

module ADP.Fusion.GAPlike.DevelCommon where

import qualified Data.PrimitiveArray as PA
import qualified Data.Vector.Unboxed as VU

import Data.PrimitiveArray.Unboxed.VectorZero as UVZ
import Data.PrimitiveArray.Unboxed.Zero as UZ
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape



dvu = VU.fromList $ concat $ replicate 10 ['a'..'z']
{-# NOINLINE dvu #-}

type PAT = UVZ.Arr0 DIM2 Int
pat :: PAT
pat = PA.fromAssocs (Z:.0:.0) (Z:.1000:.1000) 0 [(Z:.i:.j,j-i) | i <-[0..1000], j<-[i..1000] ]
{-# NOINLINE pat #-}

