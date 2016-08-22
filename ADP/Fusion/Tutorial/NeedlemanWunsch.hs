
{-# Options_GHC -fno-warn-unused-imports #-}

{-|

The Needleman-Wunsch global alignment algorithm. This algorithm is
extremely simple but provides a good showcase for what ADPfusion offers.

 -}

module ADP.Fusion.Tutorial.NeedlemanWunsch
  (
  -- * Introduction
  -- $introduction

  -- * Module Header
  -- $header
  ) where

import ADP.Fusion.Point

{- $introduction

-}

{- $header

> module Main where
>
> import           Control.Applicative
> import           Control.Monad
> import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
> import           Data.Vector.Fusion.Util
> import           Debug.Trace
> import qualified Control.Arrow as A
> import qualified Data.Vector as V
> import qualified Data.Vector.Fusion.Stream.Monadic as SM
> import qualified Data.Vector.Unboxed as VU
> import           System.Environment (getArgs)
> import           System.IO.Unsafe (unsafePerformIO)
> import           Text.Printf

@Data.PrimitiveArray@ contains data structures, and index structures for
dynamic programming. Notably, the primitive arrays holding the cell data
with Boxed and Unboxed tables. In addition, linear, context-free, and set
data structures are made available.

> import           Data.PrimitiveArray as PA hiding (map)

@ADP.Fusion@ exposes everything necessary for higher-level DP algorithms.

> import           ADP.Fusion.Point




-}
