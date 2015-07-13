
module ADP.Fusion.Term.Chr.Type where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base


-- | A generic Character parser that reads a single character but allows
-- passing additional information.
--
--  'Chr' expects a function to retrieve @r@ at index position, followed by
--  the actual generic vector with data.

data Chr r x where
  Chr :: VG.Vector v x
      => (v x -> Int -> r)
      -> (v x)
      -> Chr r x

-- | smart constructor for regular 1-character parsers

chr :: VG.Vector v x => v x -> Chr x x
chr = Chr VG.unsafeIndex
{-# Inline chr #-}

-- | Smart constructor for Maybe Peeking, followed by a character.

chrLeft xs = Chr f xs where
  f xs k = ( xs VG.!? (k-1)
           , VG.unsafeIndex xs k
           )
  {-# Inline [0] f #-}
{-# Inline chrLeft #-}

instance Build (Chr r x)

instance
  ( Element ls i
  ) => Element (ls :!: Chr r x) i where
    data Elm (ls :!: Chr r x) i = ElmChr !r !i !i !(Elm ls i)
    type Arg (ls :!: Chr r x)   = Arg ls :. r
    getArg (ElmChr x _ _ ls) = getArg ls :. x
    getIdx (ElmChr _ i _ _ ) = i
    getOmx (ElmChr _ _ o _ ) = o
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getOmx #-}

deriving instance (Show i, Show r, Show (Elm ls i)) => Show (Elm (ls :!: Chr r x) i)

type instance TermArg (TermSymbol a (Chr r x)) = TermArg a :. r

