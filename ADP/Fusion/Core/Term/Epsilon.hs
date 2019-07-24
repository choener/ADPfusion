
-- | 'Epsilon' is a global or local starting (or ending, depending on the view)
-- point for a grammar.

module ADP.Fusion.Core.Term.Epsilon where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



data LocalGlobal = Local | Global

data Epsilon (lg ∷ LocalGlobal) = Epsilon

instance Build (Epsilon lg)

instance (Element ls i) => Element (ls :!: Epsilon lg) i where
  data Elm (ls :!: Epsilon lg) i = ElmEpsilon !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: Epsilon lg)   = Arg ls :. ()
  getArg (ElmEpsilon _ l) = getArg l :. ()
  getIdx (ElmEpsilon i _) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

type instance TermArg (Epsilon lg) = ()

