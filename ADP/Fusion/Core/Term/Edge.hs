
module ADP.Fusion.Core.Term.Edge where

import Data.Strict.Tuple
import Data.Proxy

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



newtype From = From { getFrom :: Int }
  deriving (Eq,Ord,Show)

newtype To = To { getTo :: Int }
  deriving (Eq,Ord,Show)

-- | An edge in a graph. As a parsing symbol, it will provide (From:.To)
-- pairs.

data Edge = Edge

instance Build Edge

instance
  ( Element ls i
  ) => Element (ls :!: Edge) i where
    data Elm (ls :!: Edge) i = ElmEdge !(From:.To) !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Edge)   = Arg ls :. (From:.To)
    getArg (ElmEdge e _ ls) = getArg ls :. e
    getIdx (ElmEdge _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: Edge) i)

type instance TermArg Edge = (From:.To)

-- | 'edgeFromTo' creates a @(From:.To)@ structure for edges. How this is
-- filled depends on the @Proxy@. Possible are @Proxy First@ and @Proxy Last@.
-- @First@ denotes that @To@ is the first node to be visited. I.e. @First(From)
-- → Set(To)@. @Last@ on the other hand is @Set(From) → Last(To)@.

class EdgeFromTo k where
  edgeFromTo ∷ Proxy k → SetBoundary → NewBoundary → (From:.To)

newtype SetBoundary = SetBoundary Int

newtype NewBoundary = NewBoundary Int

---- | In case our sets have a @First@ boundary, then we always point from
---- the boundary "into" the set. Hence @SetNode == To@ and @NewNode ==
---- From@.
--
--instance EdgeFromTo First where
--  edgeFromTo Proxy (SetNode to) (NewNode from) = From from :. To to
--  {-# Inline edgeFromTo #-}

-- | And if the set has a @Last@ boundary, then we point from somewhere in
-- the set @To@ the @NewNode@, which is @Last@.

instance EdgeFromTo Last where
  edgeFromTo Proxy (SetBoundary from) (NewBoundary to) = From from :. To to
  {-# Inline edgeFromTo #-}

