
-- | Instances to allow 'Subword's to be used as index structures in
-- @ADPfusion@.

module ADP.Fusion.Base.Subword where

import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map)
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
  type Context (Outside Subword) = OutsideContext (Int:.Int)
  initialContext _ = OStatic (0:.0)
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

instance (Monad m) => MkStream m S (Outside Subword) where
  mkStream S (OStatic (di:.dj)) (O (Subword (_:.h))) (O (Subword (i:.j)))
    = staticCheck (i==0 && j+dj==h) . singleton $ ElmS (O $ subword i j) (O $ Subword (i:.j+dj))
  mkStream S (OFirstLeft (di:.dj)) (O (Subword (_:.h))) (O (Subword (i:.j)))
    = let i' = i-di
      in  staticCheck (0 <= i' && i<=j && j+dj<=h) . singleton $ ElmS (O $ subword i' i') (O $ subword i' i')
  mkStream S (OLeftOf (di:.dj)) (O (Subword (_:.h))) (O (Subword (i:.j)))
    = let i' = i-di
      in  staticCheck (0 <= i' && i<=j && j+dj<=h)
    $ map (\k -> ElmS (O $ subword 0 k) (O $ subword k j))
    $ enumFromStepN 0 1 (i'+1)
  {-# Inline mkStream #-}

