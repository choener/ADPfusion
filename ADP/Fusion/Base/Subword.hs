
-- | Instances to allow 'Subword's to be used as index structures in
-- @ADPfusion@.

module ADP.Fusion.Base.Subword where

import Data.Vector.Fusion.Stream.Monadic (singleton)
import Data.Vector.Fusion.Stream.Size
import Debug.Trace
import Prelude hiding (map,filter)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext Subword where
  type Context Subword = InsideContext
  initialContext _ = IStatic
  {-# Inline initialContext #-}

instance RuleContext (Outside Subword) where
  type Context (Outside Subword) = OutsideContext Subword
  initialContext = OStatic . unO
  {-# Inline  initialContext #-}

-- TODO write instance

-- instance RuleContext (Complement Subword)



instance (Monad m) => MkStream m S Subword where
  mkStream S IStatic (Subword (_:.h)) (Subword (i:.j))
    = staticCheck (0==i && i==j) . singleton $ ElmS (subword 0 0) (subword 0 0)
  mkStream S IVariable (Subword (_:.h)) (Subword (i:.j))
    = staticCheck (0<=i && i<=j && j<=h) . singleton $ ElmS (subword i j) (subword 0 0)
  {-# Inline mkStream #-}

-- TODO write instance

-- instance (Monad m) => MkStream m S (Outside Subword) where
