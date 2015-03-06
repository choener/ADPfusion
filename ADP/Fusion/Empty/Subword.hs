
module ADP.Fusion.Empty.Subword where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Empty.Type

import Data.Vector.Fusion.Util



instance
  ( Monad m
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Empty) Subword where
  mkStream (ls :!: Empty) IStatic hh (Subword (i:.j))
    = staticCheck (i==j)
    $ S.map (ElmEmpty (subword i j) (subword 0 0))
    $ mkStream ls IStatic hh (subword i j)
  {-# Inline mkStream #-}
