
module ADPfusion.Core.Term.Str where

import           Data.Strict.Tuple
import           GHC.TypeLits
import           GHC.TypeNats
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADPfusion.Core.Classes
import           ADPfusion.Core.Multi



-- | A @Str@ wraps an input vector and provides type-level annotations on
-- linked @Str@'s, their minimal and maximal size.
--
-- If @linked ∷ Symbol@ is set to @Just aName@, then all @Str@'s that are
-- part of the same rule share their size information. This allows rules of the
-- kind @X -> a Y b@ where @a,b@ have a common maximal size.
--
-- @minSz@ and @maxSz@ provide minimal and maximal parser width, if set.
--
-- TODO consider if @maxSz@ could do with just @Nat@

data Str (linked :: Symbol) (minSz :: Nat) (maxSz :: Maybe Nat) v x (r :: *) where
  Str :: VG.Vector v x
      => (Int -> Int -> v x -> r)
      -> !(v x)
      -> Str linked minSz maxSz v x r

str :: VG.Vector v x => v x -> Str linked minSz maxSz v x (v x)
str = Str (\i j -> VG.unsafeSlice i (j-i))
{-# Inline str #-}

-- | Construct string parsers with no special constraints.

manyV :: VG.Vector v x => v x → Str "" 0 Nothing v x (v x)
manyV = Str (\i j -> VG.unsafeSlice i (j-i))
{-# Inline manyV #-}

someV :: VG.Vector v x => v x → Str "" 1 Nothing v x (v x)
someV = Str (\i j -> VG.unsafeSlice i (j-i))
{-# Inline someV #-}

strContext :: VG.Vector v x => v x -> Str linked minSz maxSz v x (v x,v x, v x)
strContext = Str (\i j xs -> (VG.unsafeTake i xs, VG.unsafeSlice i (j-i) xs, VG.unsafeDrop j xs))
{-# Inline strContext #-}

-- TODO really need to be able to remove this system. Forgetting @Build@ gives
-- very strange type errors.

instance Build (Str linked minSz maxSz v x r)

instance
  ( Element ls i
  , VG.Vector v x
  ) => Element (ls :!: Str linked minSz maxSz v x r) i where
    data Elm (ls :!: Str linked minSz maxSz v x r) i = ElmStr !r !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Str linked minSz maxSz v x r)   = Arg ls :. r
    type RecElm (ls :!: Str linked minSz maxSz v x r) i = Elm (ls :!: Str linked minSz maxSz v x r) i
    getArg (ElmStr x _ ls) = getArg ls :. x
    getIdx (ElmStr _ i _ ) = i
    getElm = id
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (v x), Show (Elm ls i), Show r) => Show (Elm (ls :!: Str linked minSz maxSz v x r) i)

type instance TermArg (Str linked minSz maxSz v x r) = r

