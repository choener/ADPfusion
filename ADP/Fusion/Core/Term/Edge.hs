
module ADP.Fusion.Core.Term.Edge where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



newtype From = From { getFrom :: Int }
  deriving (Eq,Ord,Show)

newtype To = To { getTo :: Int }
  deriving (Eq,Ord,Show)

-- | An edge in a graph. As a parsing symbol, it will provide (From:.To)
-- pairs.

data Edge = Edge

instance Build Edge

instance
  ( Element ls i
  ) => Element (ls :!: Edge) i where
    data Elm (ls :!: Edge) i = ElmEdge !(From:.To) !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Edge)   = Arg ls :. (From:.To)
    getArg (ElmEdge e _ ls) = getArg ls :. e
    getIdx (ElmEdge _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: Edge) i)

type instance TermArg Edge = (From:.To)

