
module ADP.Fusion.Term.Epsilon.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



data Epsilon = Epsilon

instance Build Epsilon

instance (Element ls i) => Element (ls :!: Epsilon) i where
  data Elm (ls :!: Epsilon) i = ElmEpsilon !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: Epsilon)   = Arg ls :. ()
  getArg (ElmEpsilon _ l) = getArg l :. ()
  getIdx (ElmEpsilon i _) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

type instance TermArg Epsilon = ()

