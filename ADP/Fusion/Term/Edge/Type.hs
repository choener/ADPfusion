
module ADP.Fusion.Term.Edge.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



data Edge e where
  Edge :: (Int -> Int -> e) -> Edge e

instance Build (Edge e)

instance
  ( Element ls i
  ) => Element (ls :!: Edge e) i where
    data Elm (ls :!: Edge e) i = ElmEdge !e !i !i (Elm ls i)
    type Arg (ls :!: Edge e)   = Arg ls :. e
    getArg (ElmEdge e _ _ ls) = getArg ls :. e
    getIdx (ElmEdge _ i _ _ ) = i
    getOmx (ElmEdge _ _ o _ ) = o
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getOmx #-}

deriving instance (Show i, Show e, Show (Elm ls i)) => Show (Elm (ls :!: Edge e) i)

type instance TermArg (TermSymbol a (Edge e)) = TermArg a :. e

