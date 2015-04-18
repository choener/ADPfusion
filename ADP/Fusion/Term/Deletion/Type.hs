
module ADP.Fusion.Term.Deletion.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



data Deletion = Deletion

instance Build Deletion

instance (Element ls i) => Element (ls :!: Deletion) i where
  data Elm (ls :!: Deletion) i = ElmDeletion !i !i !(Elm ls i)
  type Arg (ls :!: Deletion)   = Arg ls :. ()
  getArg (ElmDeletion _ _ l) = getArg l :. ()
  getIdx (ElmDeletion i _ _) = i
  getOmx (ElmDeletion _ o _) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

type instance TermArg (TermSymbol a Deletion) = TermArg a :. ()

