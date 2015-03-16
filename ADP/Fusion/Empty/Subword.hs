
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
  mkStream (ls :!: Empty) IStatic hh ij@(Subword (i:.j))
    = staticCheck (i==j)
    $ S.map (ElmEmpty (subword i j) (subword 0 0))
    $ mkStream ls IStatic hh ij
  {-# Inline mkStream #-}



instance
  ( Monad m
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: Empty) (Outside Subword) where

