
module ADP.Fusion.Term.Strng.Subword where


import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Strng.Type



instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Strng v x) Subword where


