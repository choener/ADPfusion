
-- |
--
-- TODO Rename @Chr@ to @Vtx@, a vertex parser is a generalization of
-- a char parser. But this is only semantics, so not super important to do
-- now.

module ADP.Fusion.Core.Term.MultiChr where

import           Data.Strict.Tuple
import           GHC.TypeNats
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Core.Classes
import           ADP.Fusion.Core.Multi



-- | A generic Character parser that reads a single character but allows
-- passing additional information.
--
--  'Chr' expects a function to retrieve @r@ at index position, followed by
--  the actual generic vector with data.

data MultiChr (c ∷ Nat) v x where
  MultiChr ∷ VG.Vector v x
           ⇒ !(v x)
           → MultiChr c v x

-- | smart constructor for regular 1-character parsers

multiChr :: VG.Vector v x => v x -> MultiChr c v x
multiChr = MultiChr
{-# Inline multiChr #-}

instance Build (MultiChr c v x)

instance
  ( Element ls i
  ) => Element (ls :!: MultiChr c v x) i where
    data Elm (ls :!: MultiChr c v x) i = ElmMultiChr !(v x) !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: MultiChr c v x)   = Arg ls :. v x
    getArg (ElmMultiChr x _ ls) = getArg ls :. x
    getIdx (ElmMultiChr _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (v x), Show (Elm ls i)) => Show (Elm (ls :!: MultiChr c v x) i)

type instance TermArg (MultiChr c v x) = v x

