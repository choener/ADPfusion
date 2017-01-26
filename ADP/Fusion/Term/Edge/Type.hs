
module ADP.Fusion.Term.Edge.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



newtype From = From { getFrom :: Int }

newtype To = To { getTo :: Int }

-- | An edge in a graph. The function @From -> To -> e@ is a new-typed
-- lookup function to make explicit in which order arguments are to be
-- given.

data Edge e where
  Edge :: (From -> To -> e) -> Edge e

instance Build (Edge e)

instance
  ( Element ls i
  ) => Element (ls :!: Edge e) i where
    data Elm (ls :!: Edge e) i = ElmEdge !e !(RunningIndex i) (Elm ls i)
    type Arg (ls :!: Edge e)   = Arg ls :. e
    getArg (ElmEdge e _ ls) = getArg ls :. e
    getIdx (ElmEdge _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show e, Show (Elm ls i)) => Show (Elm (ls :!: Edge e) i)

type instance TermArg (Edge e) = e

