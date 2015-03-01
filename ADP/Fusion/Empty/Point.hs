
module ADP.Fusion.Empty.Point where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Empty.Type



instance
  ( Monad m
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Empty) PointL where
  mkStream (ls :!: Empty) IStatic (PointL u) (PointL i)
    = S.map (ElmEmpty (PointL i) (PointL 0))
    $ mkStream ls IStatic (PointL u) (PointL i)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: Empty) (Outside PointL) where
  mkStream (ls :!: Empty) (OStatic d) (O (PointL u)) (O (PointL i))
    = S.map (\z -> ElmEmpty (O $ PointL i) (getOmx z) z)
    $ mkStream ls (OStatic d) (O $ PointL u) (O $ PointL i)
  {-# Inline mkStream #-}

