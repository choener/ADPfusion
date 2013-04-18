{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.DeepSeq
import Data.Array.Repa.Index
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Point
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion.Apply
import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.Region
import ADP.Fusion.Table
import ADP.Fusion.Term
import ADP.Fusion


main = do
{-
  l <- getLine
  print l
  let rl = read l :: Int
--  mapM_ test [0 .. rl]
  x <- (l,rl) `deepseq` test rl
  -}
  return ()
--  print x

{-
gnargs (Z:.Subword (i:.j)) = do
    let ix = Z :. subword i j
    let xs = VU.fromList [0 .. 100 :: Int]
    let mtable xs = MTable Tmany xs
    mxs :: (PA.MU IO (Z:.Subword) Int) <- PA.fromListM (Z:. Subword (0:.0)) (Z:. Subword (0:.100)) [0 .. ]
    let mt = mtable mxs
    zs <- (\x (Z:.a) -> x+a) <<< mt % Term (T:.Chr xs) ... SM.foldl' (+) 0 $ ix
    ix `seq` mxs `seq` mt `seq` return zs
{-# NOINLINE gnargs #-}
-}

gnargs (Z:.Point i) = do
    mxs :: (PA.MU IO (Z:.Point) Int) <- PA.fromListM (Z:.Point 0) (Z:.Point 100) [0 .. ]
    let mtable xs = MTable Eall xs
    let mt = mtable mxs
    let ix = Z :. Point i
    let xs = VU.fromList [0 .. 100 :: Int]
    zs <- (,) <<< mt % Term (T:.Chr xs) ... SM.toList $ ix
    ix `seq` mxs `seq` mt `seq` return zs
{-# NOINLINE gnargs #-}

