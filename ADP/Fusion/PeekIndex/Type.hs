
module ADP.Fusion.PeekIndex.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



data PeekIndex i = PeekIndex

instance Build (PeekIndex i)

instance
  ( Element ls i
  ) => Element (ls :!: PeekIndex i) i where
    data Elm (ls :!: PeekIndex i) i = ElmPeekIndex !i !i !(Elm ls i)
    type Arg (ls :!: PeekIndex i)   = Arg ls :. (i :. i)
    getArg (ElmPeekIndex i o ls)    = getArg ls :. (i:.o)
    getIdx (ElmPeekIndex i _ _ )    = i
    getOmx (ElmPeekIndex _ o _ )    = o
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getOmx #-}

deriving instance (Show i, Show (Elm ls i)) => Show (Elm (ls :!: PeekIndex i) i)

type instance TermArg (TermSymbol a (PeekIndex i)) = TermArg a :. PeekIndex i

