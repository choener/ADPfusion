
-- | Instances to allow 'Subword's to be used as index structures in
-- @ADPfusion@.

module ADP.Fusion.Base.Subword where

import Data.Vector.Fusion.Stream.Monadic (singleton,filter)
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
    = staticCheck (i>=0 && i==j && j<=h) . singleton $ ElmS (subword i i) (subword 0 0)
  -- NOTE it seems that a static check within an @IVariable@ context
  -- destroys fusion; maybe because of the outer flatten? We don't actually
  -- need a static check anyway because the next flatten takes care of
  -- conditional checks. @filter@ on the other hand, does work.
  -- TODO test with and without filter using quickcheck
  mkStream S IVariable (Subword (_:.h)) (Subword (i:.j))
    = filter (const $ 0<=i && i<=j && j<=h) . singleton $ ElmS (subword i i) (subword 0 0)
  {-# Inline mkStream #-}

-- TODO write instance

-- instance (Monad m) => MkStream m S (Outside Subword) where
