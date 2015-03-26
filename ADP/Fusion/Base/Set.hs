
module ADP.Fusion.Base.Set where

import Data.PrimitiveArray

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext (BS2I First Last) where
  type Context (BS2I First Last) = InsideContext
  initialContext _ = IStatic
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
  ) => MkStream m S (BS2I First Last) where

instance
  ( Monad m
  ) => MkStream m S (Outside (BS2I First Last)) where

instance
  ( Monad m
  ) => MkStream m S (Complement (BS2I First Last)) where

