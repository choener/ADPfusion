
module ADP.Fusion.Core.Term.Str where

import           Data.Strict.Tuple
import           GHC.TypeLits
import           GHC.TypeNats
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Core.Classes
import           ADP.Fusion.Core.Multi



-- | A @Str@ wraps an input vector and provides type-level annotations on
-- linked @Str@'s, their minimal and maximal size.
--
-- If @linked ∷ Maybe Symbol@ is set to @Just aName@, then all @Str@'s that are
-- part of the same rule share their size information. This allows rules of the
-- kind @X -> a Y b@ where @a,b@ have a common maximal size.
--
-- @minSz@ and @maxSz@ provide minimal and maximal parser width, if set.
--
-- TODO consider if @maxSz@ could do with just @Nat@

data Str (linked ∷ Maybe Symbol) (minSz ∷ Nat) (maxSz ∷ Maybe Nat) v x where
  Str ∷ VG.Vector v x
      ⇒ !(v x)
      → Str linked minSz maxSz v x

-- | Construct string parsers with no special constraints.

manyV ∷ VG.Vector v x ⇒ v x → Str Nothing 0 Nothing v x
manyV = Str
{-# Inline manyV #-}

someV ∷ VG.Vector v x ⇒ v x → Str Nothing 1 Nothing v x
someV = Str
{-# Inline someV #-}

instance
  ( Element ls i
  , VG.Vector v x
  ) => Element (ls :!: Str linked minSz maxSz v x) i where
    data Elm (ls :!: Str linked minSz maxSz v x) i = ElmStr !(v x) !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Str linked minSz maxSz v x)   = Arg ls :. v x
    getArg (ElmStr x _ ls) = getArg ls :. x
    getIdx (ElmStr _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (v x), Show (Elm ls i)) => Show (Elm (ls :!: Str linked minSz maxSz v x) i)

type instance TermArg (Str linked minSz maxSz v x) = v x

