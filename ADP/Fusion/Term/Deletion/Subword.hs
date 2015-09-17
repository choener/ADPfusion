
module ADP.Fusion.Term.Deletion.Subword where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Deletion.Type



instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Deletion) (is:.Subword I) where
  terminalStream (a:|Deletion) (sv:.IStatic _) (is:.ij@(Subword (i:.j)))
    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.subword j j) (os:.subword 0 0) (e:.()))
    . iPackTerminalStream a sv (is:.ij)
  terminalStream (a:|Deletion) (sv:.IVariable _) (is:.ij@(Subword (i:.j)))
    = S.map (\(S6 s (zi:.Subword (_:.l)) (zo:._) is os e) -> S6 s zi zo (is:.subword l l) (os:.subword 0 0) (e:.()))
    . iPackTerminalStream a sv (is:.ij)
  {-# Inline terminalStream #-}

instance TermStaticVar Deletion (Subword I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ ij = ij
  {-# Inline termStaticVar   #-}
  {-# Inline termStreamIndex #-}

