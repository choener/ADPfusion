
module ADP.Fusion.Term.Test.Type where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Core.Classes
import           ADP.Fusion.Core.Multi



-- | 'Test' terminals return "strings", i.e. vectors of @Chr@s. They allow
-- the user to specify @[ 0 .. ]@ atoms to be parsed at once. It is
-- possible to both, limit the minimal and maximal number.
--
-- NOTE gadt comments are not parsed by haddock?

{-
data Test v x where
  Test :: VG.Vector v x
        => (Int -> Int -> v x -> v x)  -- @slice@ function
        -> Int                         -- minimal size
        -> Int                         -- maximal size (just use s.th. big if you don't want a limit)
        -> (v x)                       -- the actual vector
        -> Test v x

manyS :: VG.Vector v x => v x -> Test v x
manyS = \xs -> Test VG.unsafeSlice 0 (VG.length xs) xs
{-# Inline manyS #-}

someS :: VG.Vector v x => v x -> Test v x
someS = \xs -> Test VG.unsafeSlice 1 (VG.length xs) xs
{-# Inline someS #-}

strng :: VG.Vector v x => Int -> Int -> v x -> Test v x
strng = \minL maxL xs -> Test VG.unsafeSlice minL maxL xs
{-# Inline strng #-}
-}

data Test v x where
  Test :: VG.Vector v x => v x -> Test v x

instance Build (Test v x)

instance
  ( Element ls i
  ) => Element (ls :!: Test v x) i where
  data Elm (ls :!: Test v x) i = ElmTest !(v x) !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: Test v x)   = Arg ls :. v x
  getArg (ElmTest x _ ls) = getArg ls :. x
  getIdx (ElmTest _ i _ ) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (v x), Show (Elm ls i)) => Show (Elm (ls :!: Test v x) i)

type instance TermArg (Test v x) = v x

