
module ADP.Fusion.None.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



data None = None

instance Build None

instance (Element ls i) => Element (ls :!: None) i where
  data Elm (ls :!: None) i = ElmNone !i !i !(Elm ls i)
  type Arg (ls :!: None)   = Arg ls :. ()
  getArg (ElmNone _ _ l) = getArg l :. ()
  getIdx (ElmNone i _ _) = i
  getOmx (ElmNone _ o _) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

type instance TermArg (TermSymbol a None) = TermArg a :. ()

