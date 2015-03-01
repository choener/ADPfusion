
module ADP.Fusion.Empty.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



data Empty = Empty

instance Build Empty

instance (Element ls i) => Element (ls :!: Empty) i where
  data Elm (ls :!: Empty) i = ElmEmpty !i !i !(Elm ls i)
  type Arg (ls :!: Empty)   = Arg ls :. ()
  getArg (ElmEmpty _ _ l) = getArg l :. ()
  getIdx (ElmEmpty i _ _) = i
  getOmx (ElmEmpty _ o _) = o
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

