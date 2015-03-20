
module ADP.Fusion.Empty.Subword where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Empty.Type

--import Data.Vector.Fusion.Util



instance
  ( Monad m
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Empty) Subword where
  mkStream (ls :!: Empty) IStatic hh ij@(Subword (i:.j))
    = staticCheck (i==j)
    $ map (ElmEmpty (subword i j) (subword 0 0))
    $ mkStream ls IStatic hh ij
  {-# Inline mkStream #-}



instance
  ( Monad m
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: Empty) (Outside Subword) where
  mkStream (ls :!: Empty) (OStatic d) u ij@(O (Subword (i:.j)))
    = map (ElmEmpty (O $ subword i j) (O $ subword i j))
    $ mkStream ls (OStatic d) u ij
  {-# Inline mkStream #-}

