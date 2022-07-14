
module ADPfusion.Core.Term.Str where

import           Data.Proxy
import           Data.Strict.Tuple
import           Data.Type.Equality
import           GHC.TypeLits
import           GHC.TypeNats ()
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
      => (v x -> Int -> Int -> r)
      -> !(v x)
      -> Str linked minSz maxSz v x r

str :: VG.Vector v x => v x -> Str linked minSz maxSz v x (v x)
{-# Inline str #-}
str = Str (\xs i j -> VG.unsafeSlice i (j-i) xs)

-- | Construct string parsers with no special constraints.

manyV :: VG.Vector v x => v x → Str "" 0 Nothing v x (v x)
{-# Inline manyV #-}
manyV = Str f
  where f = (\xs i j -> VG.unsafeSlice i (j-i) xs)
        {-# Inline [0] f #-}

someV :: VG.Vector v x => v x → Str "" 1 Nothing v x (v x)
{-# Inline someV #-}
someV = Str (\xs i j -> VG.unsafeSlice i (j-i) xs)

strContext :: VG.Vector v x => v x -> Str linked minSz maxSz v x (v x,v x, v x)
{-# Inline strContext #-}
strContext = Str f
  where f = (\xs i j -> (VG.unsafeTake i xs, VG.unsafeSlice i (j-i) xs, VG.unsafeDrop j xs))
        {-# Inline [0] f #-}

-- | This parser always parses strings of length @0@, its use is in peeking at the split point.

strPeek :: VG.Vector v x => v x -> Str "" 0 (Just 0) v x (v x, v x)
{-# Inline strPeek #-}
strPeek = Str f
  where f = (\xs i j -> VG.splitAt i xs)
        {-# Inline [0] f #-}



-- | This class provides the machinery to calculate the total size of linked string parsers.

class LinkedSz (eqEmpty::Bool) (p::Symbol) ts i where
  -- | Given a recursive @Elm@ structure, 'linkedSz' returns the number of terminals that have been
  -- parsed by 'Str' parsers with the same @linked@ tag.
  linkedSz :: Proxy eqEmpty -> Proxy p -> Elm ts i -> Int

-- | Stop linked size recursion at @S@.

instance LinkedSz False linked (Term1 (Elm S anyIx)) anyFullIx where
  {-# Inline linkedSz #-}
  linkedSz _ _ _ = 0

-- | If the @Str@ we want to calculate for has a symbol @""@ then there is no need to sum up the
-- linked sizes, since "" declares independence.
--
-- @True@ here means that @p==""@ and we do NOT have linked strings.

instance LinkedSz True p any i where
  {-# Inline linkedSz #-}
  linkedSz _ _ _ = 0

-- | We have an instance of the @linked@ tag being non-empty (@False@) and now need to call the
-- actual size calculation implementation via @linkedSzEq@.

instance (eq ~ (p == linked), LinkedSzEq eq p (ls :!: Str linked minSz maxSz v x r) i )
  => LinkedSz False p (ls :!: Str linked minSz maxSz v x r) i where
  {-# Inline linkedSz #-}
  linkedSz _ _ ts = linkedSzEq (Proxy @eq) (Proxy @p) ts

-- | This class calculates the actual link sizes.

class LinkedSzEq (eq::Bool) (p::Symbol) ts i where
  linkedSzEq :: Proxy eq -> Proxy p -> Elm ts i -> Int





-- | This class handles maximal-size constraints.

class MaybeMaxSz (maxSz :: Maybe Nat) where
  -- | If the first argument is @<= maxSz@, then we return @Just@ the value, otherwise nothing.
  maybeMaxSz :: Proxy maxSz -> Int -> a -> Maybe a
  -- | @greater@ check for @maxSz@.
  gtMaxSz :: Proxy maxSz -> Int -> Bool

-- | No maximal size constraint, 'maybeMaxSz' shall always return @Just@ with the value, while
-- @gtMaxSz@ is always @False@.

instance MaybeMaxSz Nothing where
  {-# Inline maybeMaxSz #-}
  maybeMaxSz _ _ = Just
  {-# Inline gtMaxSz #-}
  gtMaxSz _ _ = False

-- | A maximal size constriant was given, and @maybeMaxSz@ will let pass only values @<= maxSz@ with
-- a @Just value@, while @gtMaxSz@ checks if the value is @> maxSz@.

instance (KnownNat maxSz) => MaybeMaxSz (Just maxSz) where
  {-# Inline maybeMaxSz #-}
  maybeMaxSz _ k a
    | k <= maxSz = Just a
    | otherwise  = Nothing
    where maxSz = fromIntegral (natVal (Proxy :: Proxy maxSz))
  {-# Inline gtMaxSz #-}
  gtMaxSz _ k = k > fromIntegral (natVal (Proxy :: Proxy maxSz))


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

