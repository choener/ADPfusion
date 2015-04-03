
-- | The @Context@ for a @BitSet@ is the number of bits we should reserve
-- for the more right-most symbols, which request a number of reserved
-- bits.

module ADP.Fusion.Base.Set where

import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Data.Vector.Fusion.Stream.Size
import Debug.Trace
import Prelude hiding (map,filter)
import Data.Bits

import Data.PrimitiveArray

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext BitSet where
  type Context BitSet = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (Outside BitSet) where
  type Context (Outside BitSet) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}

instance RuleContext (Complement BitSet) where
  type Context (Complement BitSet) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}

instance RuleContext (BS2I First Last) where
  type Context (BS2I First Last) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (Outside (BS2I First Last)) where
  type Context (Outside (BS2I First Last)) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}

instance RuleContext (Complement (BS2I First Last)) where
  type Context (Complement (BS2I First Last)) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



instance
  ( Monad m
  ) => MkStream m S BitSet where
  mkStream S (IStatic c) u s
    = staticCheck (c <= popCount s) . singleton $ ElmS s 0
  mkStream S (IVariable c) u s
    = staticCheck (c <= popCount s) . singleton $ ElmS 0 0
  {-# Inline mkStream #-}


instance
  ( Monad m
  ) => MkStream m S (BS2I First Last) where

instance
  ( Monad m
  ) => MkStream m S (Outside (BS2I First Last)) where

instance
  ( Monad m
  ) => MkStream m S (Complement (BS2I First Last)) where



-- | An undefined bitset with 2 interfaces.

undefbs2i :: BS2I f l
undefbs2i = BitSet (-1) :> Interface (-1) :> Interface (-1)
{-# Inline undefbs2i #-}

undefi :: Interface i
undefi = Interface (-1)
{-# Inline undefi #-}

