
module ADP.Fusion.Term.Strng.Type where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base



-- | 'Strng' terminals return "strings", i.e. vectors of @Chr@s. They allow
-- the user to specify @[ 0 .. ]@ atoms to be parsed at once. It is
-- possible to both, limit the minimal and maximal number.

data Strng v x where
  Strng :: VG.Vector v x
        => !(Int -> Int -> v x -> v x)  -- ^ @slice@ function
        -> !Int                         -- ^ minimal size
        -> !Int                         -- ^ maximal size (just use s.th. big if you don't want a limit)
        -> !(v x)                       -- ^ the actual vector
        -> Strng v x

strng xs = Strng VG.unsafeSlice xs
{-# Inline strng #-}

instance Build (Strng v x)

instance
  ( Element ls i
  ) => Element (ls :!: Strng v x) i where
  data Elm (ls :!: Strng v x) i = ElmStrng !(v x) !i !i !(Elm ls i)
  type Arg (ls :!: Strng v x)   = Arg ls :. v x
  getArg (ElmStrng x _ _ ls) = getArg ls :. x
  getIdx (ElmStrng _ i _ _ ) = i
  getOmx (ElmStrng _ _ o _ ) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

deriving instance (Show i, Show (v x), Show (Elm ls i)) => Show (Elm (ls :!: Strng v x) i)

type instance TermArg (TermSymbol a (Strng v x)) = TermArg a :. v x

