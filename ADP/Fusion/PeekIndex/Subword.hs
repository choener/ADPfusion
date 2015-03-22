
module ADP.Fusion.PeekIndex.Subword where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic (map)
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.PeekIndex.Type



instance
  ( Monad m
  , Element ls (Complement Subword)
  , MkStream m ls (Complement Subword)
  ) => MkStream m (ls :!: PeekIndex (Complement Subword)) (Complement Subword) where
  mkStream (ls :!: PeekIndex) Complemented h ij
    = map (\s -> ElmPeekIndex (getIdx s) (getOmx s) s)
    $ mkStream ls Complemented h ij
  {-# Inline mkStream #-}

