
module ADP.Fusion.Term.Strng.Type where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Core.Classes
import           ADP.Fusion.Core.Multi



-- | 'Strng' terminals return "strings", i.e. vectors of @Chr@s. They allow
-- the user to specify @[ 0 .. ]@ atoms to be parsed at once. It is
-- possible to both, limit the minimal and maximal number.
--
-- NOTE gadt comments are not parsed by haddock?

{-
data Strng v x where
  Strng :: VG.Vector v x
        => (Int -> Int -> v x -> v x)  -- @slice@ function
        -> Int                         -- minimal size
        -> Int                         -- maximal size (just use s.th. big if you don't want a limit)
        -> (v x)                       -- the actual vector
        -> Strng v x

manyS :: VG.Vector v x => v x -> Strng v x
manyS = \xs -> Strng VG.unsafeSlice 0 (VG.length xs) xs
{-# Inline manyS #-}

someS :: VG.Vector v x => v x -> Strng v x
someS = \xs -> Strng VG.unsafeSlice 1 (VG.length xs) xs
{-# Inline someS #-}

strng :: VG.Vector v x => Int -> Int -> v x -> Strng v x
strng = \minL maxL xs -> Strng VG.unsafeSlice minL maxL xs
{-# Inline strng #-}
-}

data Strng v x where
  Strng :: VG.Vector v x => v x -> Strng v x

instance Build (Strng v x)

instance
  ( Element ls i
  ) => Element (ls :!: Strng v x) i where
  data Elm (ls :!: Strng v x) i = ElmStrng !(v x) !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: Strng v x)   = Arg ls :. v x
  getArg (ElmStrng x _ ls) = getArg ls :. x
  getIdx (ElmStrng _ i _ ) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (v x), Show (Elm ls i)) => Show (Elm (ls :!: Strng v x) i)

type instance TermArg (Strng v x) = v x

