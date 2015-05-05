
module ADP.Fusion.Term.Deletion.Point where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Deletion.Type



instance
  ( Monad m
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Deletion) PointL where
  mkStream (ls :!: Deletion) (IStatic d) (PointL u) (PointL i)
    = S.map (ElmDeletion (PointL i) (PointL 0))
    $ mkStream ls (IStatic d) (PointL u) (PointL i)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: Deletion) (Outside PointL) where
  mkStream (ls :!: Deletion) (OStatic d) (O (PointL u)) (O (PointL i))
    = S.map (\z -> ElmDeletion (O $ PointL i) (getOmx z) z)
    $ mkStream ls (OStatic d) (O $ PointL u) (O $ PointL i)
  {-# Inline mkStream #-}

instance TermStaticVar Deletion PointL where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar Deletion (Outside PointL) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Deletion) (is:.PointL) where
  terminalStream (a:|Deletion) (sv:.IStatic _) (is:.i@(PointL j))
    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.()))
    . iPackTerminalStream a sv (is:.i)
  {-# Inline terminalStream #-}

instance
  ( Monad m
  , TerminalStream m a (Outside is)
  ) => TerminalStream m (TermSymbol a Deletion) (Outside (is:.PointL)) where
  terminalStream (a:|Deletion) (sv:.OStatic d) (O (is:.i))
    = S.map (\(S6 s (zi:._) (zo:.PointL k) (O is) (O os) e) -> S6 s zi zo (O (is:.(PointL $ k-d))) (O (os:.PointL k)) (e:.()))
    . oPackTerminalStream a sv (O (is:.i))
  {-# Inline terminalStream #-}

