
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

instance TermStaticVar Empty PointL where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar Empty (Outside PointL) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Empty) (is:.PointL) where
  terminalStream (a:|Empty) (sv:.IStatic) (is:.i@(PointL j))
    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.()))
    . iPackTerminalStream a sv (is:.i)
  {-# Inline terminalStream #-}

instance
  ( Monad m
  , TerminalStream m a (Outside is)
  ) => TerminalStream m (TermSymbol a Empty) (Outside (is:.PointL)) where
  terminalStream (a:|Empty) (sv:.OStatic d) (O (is:.i))
    = S.map (\(S6 s (zi:._) (zo:.PointL k) (O is) (O os) e) -> S6 s zi zo (O (is:.(PointL $ k-d))) (O (os:.PointL k)) (e:.()))
    . oPackTerminalStream a sv (O (is:.i))
  {-# Inline terminalStream #-}

