
-- | The @Context@ for a @BitSet@ is the number of bits we should reserve
-- for the more right-most symbols, which request a number of reserved
-- bits.

module ADP.Fusion.Base.Set where

import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Debug.Trace
import Prelude hiding (map,filter)
import Data.Bits
import Data.Bits.Ordered

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



type instance TblConstraint (BitSet t)  = TableConstraint
type instance TblConstraint (BS2 i j t) = TableConstraint



instance RuleContext (BitSet I) where
  type Context (BitSet I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

-- | The @Int@ in an @OutsideContext@ counts how many bits need to be fixed
-- statically. I.e. if the bits @{1,2}@ are set in @X -> Y t@, and @t@ has
-- size @1@, then @Y@ will have @{1,2,3}@, @{1,2,4}@ and so on, with @t@
-- having @3, 4, ...@ as values.

instance RuleContext (BitSet O) where
  type Context (BitSet O) = OutsideContext Int
  initialContext _ = OStatic 0
  {-# Inline initialContext #-}

instance RuleContext (BitSet C) where
  type Context (BitSet C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



instance RuleContext (BS2 First Last I) where
  type Context (BS2 First Last I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (BS2 First Last O) where
  type Context (BS2 First Last O) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}

instance RuleContext (BS2 First Last C) where
  type Context (BS2 First Last C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



instance
  ( Monad m
  ) => MkStream m S (BitSet I) where
  -- | We enumerate all sets that have @popCount s - rb@ bits. Since we are
  -- @IStatic@ we only have static objects following. These will fill in
  -- the missing bits. Each object will fill a fixed number of bits, until
  -- @s@ has been recovered. Otherwise we would have an @IVariable@
  -- context.
  mkStream S (IStatic rb) u s
    = staticCheck (rb <= ps) . map (\k -> ElmS (popShiftL s k) 0) $ unfoldr go strt
    where strt = BitSet $ 2^(ps - rb) - 1
          ps   = popCount s
          go k = (k,) <$> popPermutation ps k
  -- | Once we are variable, we do not reserve any bits, just check that
  -- the total reservation (if any) works.
  mkStream S (IVariable rb) u s
    = staticCheck (rb <= popCount s) . singleton $ ElmS 0 0
  {-# Inline mkStream #-}

-- | Initial index construction for outside Bitsets. Bits set to @0@
-- indicate hole-space. The last bitset, the one accessed by @axiom@, is
-- @BitSet 0@.
--
-- We need to be careful with reserved bits! Reserved bits are @0@ bits
-- that can be switched to @1@. This means that @rb@ + popCount s <=
-- popCount u@.
--
-- @OStatic@'s happen when we only have terminals on the r.h.s. That is,
-- with @X -> end@.
--
-- TODO test all of this via quickcheck!

instance
  ( Monad m
  ) => MkStream m S (BitSet O) where
  -- | Same argument as above for @BitSet O@ construction.
--  mkStream S (OStatic rp) u s
--    = undefined -- staticCheck (popCount s + rp <= popCount u) . singleton $ ElmS s s
--  mkStream S (ORightOf _) u s
--    = error "ADP.Fusion.Base.Set: Entered ORightOf/BitSet"
  mkStream S (OFirstLeft rb) u s
    = staticCheck (rb + popCount s <= popCount u) . singleton $ ElmS 0 0
--  mkStream S (OLeftOf rp) u s
--    = staticCheck (popCount s + rp <= popCount u) . singleton $ ElmS s s
--  {-# Inline mkStream #-}

instance
  ( Monad m
  ) => MkStream m S (BitSet C) where

instance
  ( Monad m
  ) => MkStream m S (BS2 First Last I) where
  mkStream S (IStatic rp) u sij@(BS2 s (Iter i) _)
    = staticCheck (popCount s == 0 && rp == 0) . singleton $ ElmS (BS2 0 (Iter i) (Iter i)) undefbs2i
  mkStream S (IVariable rp) u sij@(BS2 s (Iter i) _)
    = staticCheck (popCount s >= rp) . singleton $ ElmS (BS2 0 (Iter i) (Iter i)) undefbs2i
  {-# Inline mkStream #-}

instance
  ( Monad m
  ) => MkStream m S (BS2 First Last O) where

instance
  ( Monad m
  ) => MkStream m S (BS2 First Last C) where



-- | An undefined bitset with 2 interfaces.

undefbs2i :: BS2 f l t
undefbs2i = BS2 (-1)  (-1) (-1)
{-# Inline undefbs2i #-}

undefi :: Interface i
undefi = (-1)
{-# Inline undefi #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (BitSet I) where
  tableStaticVar _ c (IStatic   d) _ = IVariable $ d - minSize c -- TODO rly?
  tableStaticVar _ _ (IVariable d) _ = IVariable $ d
  tableStreamIndex _ c _ bitSet = bitSet -- TODO rly?
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (BS2 i j I) where

-- | We sometimes need 

data ThisThatNaught a b = This a | That b | Naught

