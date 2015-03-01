
module ADP.Fusion.Table.Array.Point where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Table.Array.Type



instance
  ( Monad m
  , Element ls PointL
  , PrimArrayOps arr PointL x
  , MkStream m ls PointL
  ) => MkStream m (ls :!: ITbl m arr PointL x) PointL where
  mkStream (ls :!: ITbl c t _) IStatic (PointL u) (PointL i)
    = let ms = minSize c in seq ms $ seq t $
    S.map (ElmITbl (t ! PointL i) (PointL i) (PointL 0))
    $ mkStream ls IVariable (PointL u) (PointL $ i - ms)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , PrimArrayOps arr (Outside PointL) x
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: ITbl m arr (Outside PointL) x) (Outside PointL) where
  mkStream (ls :!: ITbl c t _) (OStatic d) (O (PointL u)) (O (PointL i))
    = let ms = minSize c in seq ms $ seq t $
    S.map (\z -> let o = getOmx z
                 in  ElmITbl (t ! o) o o z)
    $ mkStream ls (OVariable FarLeft d)  (O $ PointL u) (O $ PointL $ i - ms)
  {-# Inline mkStream #-}

