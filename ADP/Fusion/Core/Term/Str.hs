
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
-- TODO consider if @minSz@ (and possibly @maxSz@) could do with just @Nat@

data Str (linked ∷ Maybe Symbol) (minSz ∷ Maybe Nat) (maxSz ∷ Maybe Nat) x where
  Str ∷ VG.Vector v x
      ⇒ !(v x)
      → Str linked minSz maxSz x

