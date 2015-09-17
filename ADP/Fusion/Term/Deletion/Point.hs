
module ADP.Fusion.Term.Deletion.Point where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Deletion.Type



instance
  ( Monad m
  , MkStream m ls (PointL I)
  ) => MkStream m (ls :!: Deletion) (PointL I) where
  mkStream (ls :!: Deletion) (IStatic d) u i
    = S.map (ElmDeletion i (PointL 0))
    $ mkStream ls (IStatic d) u i
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (PointL O)
  , MkStream m ls (PointL O)
  ) => MkStream m (ls :!: Deletion) (PointL O) where
  mkStream (ls :!: Deletion) (OStatic d) u i
    = S.map (\z -> ElmDeletion i (getOmx z) z)
    $ mkStream ls (OStatic d) u i
  {-# Inline mkStream #-}

instance TermStaticVar Deletion (PointL I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar Deletion (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Deletion) (is:.PointL I) where
  terminalStream (a:|Deletion) (sv:.IStatic _) (is:.i@(PointL j))
    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.()))
    . iPackTerminalStream a sv (is:.i)
  {-# Inline terminalStream #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Deletion) (is:.PointL O) where
  terminalStream (a:|Deletion) (sv:.OStatic d) (is:.i)
    = S.map (\(S6 s (zi:._) (zo:.PointL k) is os e) -> S6 s zi zo (is:.(PointL $ k-d)) (os:.PointL k) (e:.()))
    . iPackTerminalStream a sv (is:.i)
  {-# Inline terminalStream #-}

