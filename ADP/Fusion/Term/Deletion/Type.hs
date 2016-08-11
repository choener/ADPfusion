
module ADP.Fusion.Term.Deletion.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



data Deletion = Deletion

instance Build Deletion

instance (Element ls i) => Element (ls :!: Deletion) i where
  data Elm (ls :!: Deletion) i = ElmDeletion !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: Deletion)   = Arg ls :. ()
  getArg (ElmDeletion _ l) = getArg l :. ()
  getIdx (ElmDeletion i _) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

type instance TermArg Deletion = ()

