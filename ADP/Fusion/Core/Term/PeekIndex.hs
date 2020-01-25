
module ADP.Fusion.Core.Term.PeekIndex where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



data PeekIndex i = PeekIndex

instance Build (PeekIndex i)

instance
  ( Element ls i
  ) => Element (ls :!: PeekIndex i) i where
    data Elm (ls :!: PeekIndex i) i = ElmPeekIndex !i !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: PeekIndex i)   = Arg ls :. i
    getArg (ElmPeekIndex x _  ls)    = getArg ls :. x
    getIdx (ElmPeekIndex _ i  _ )    = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: PeekIndex i) i)

type instance TermArg (PeekIndex i) = i

