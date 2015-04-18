
module ADP.Fusion.Term.Epsilon.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



data Epsilon = Epsilon

instance Build Epsilon

instance (Element ls i) => Element (ls :!: Epsilon) i where
  data Elm (ls :!: Epsilon) i = ElmEpsilon !i !i !(Elm ls i)
  type Arg (ls :!: Epsilon)   = Arg ls :. ()
  getArg (ElmEpsilon _ _ l) = getArg l :. ()
  getIdx (ElmEpsilon i _ _) = i
  getOmx (ElmEpsilon _ o _) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

type instance TermArg (TermSymbol a Epsilon) = TermArg a :. ()

