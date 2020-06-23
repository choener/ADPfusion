
-- | 'Epsilon' is a global or local starting (or ending, depending on the view)
-- point for a grammar.

module ADPfusion.Core.Term.Epsilon where

import Data.Data
import Data.Strict.Tuple
import Data.Typeable
import GHC.Generics(Generic)

import Data.PrimitiveArray

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi



data LocalGlobal = Local | Global
  deriving (Eq,Ord,Read,Show,Data,Typeable,Generic)

data Epsilon (lg ∷ LocalGlobal) = Epsilon

instance Build (Epsilon lg)

instance (Element ls i) => Element (ls :!: Epsilon lg) i where
  data Elm (ls :!: Epsilon lg) i = ElmEpsilon !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: Epsilon lg)   = Arg ls :. ()
  type RecElm (ls :!: Epsilon lg) i = Elm (ls :!: Epsilon lg) i
  getArg (ElmEpsilon _ l) = getArg l :. ()
  getIdx (ElmEpsilon i _) = i
  getElm = id
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

type instance TermArg (Epsilon lg) = ()

