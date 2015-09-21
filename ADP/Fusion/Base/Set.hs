
-- | The @Context@ for a @BitSet@ is the number of bits we should reserve
-- for the more right-most symbols, which request a number of reserved
-- bits.

module ADP.Fusion.Base.Set where

import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Debug.Trace
import Prelude hiding (map,filter)
import Data.Bits

import Data.PrimitiveArray

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



type instance TblConstraint (BitSet t)  = TableConstraint
type instance TblConstraint (BS2 i j t) = TableConstraint



instance RuleContext (BitSet I) where
  type Context (BitSet I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (BitSet O) where
  type Context (BitSet O) = OutsideContext ()
  initialContext _ = OStatic ()
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
  mkStream S (IStatic c) u s
    = staticCheck (c <= popCount s) . singleton $ ElmS s 0
  mkStream S (IVariable c) u s
    = staticCheck (c <= popCount s) . singleton $ ElmS 0 0
  {-# Inline mkStream #-}



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

