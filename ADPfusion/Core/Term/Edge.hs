
module ADPfusion.Core.Term.Edge where

import Data.Strict.Tuple
import Data.Proxy

import Data.PrimitiveArray

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi



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
    type RecElm (ls :!: Edge) i = Elm (ls :!: Edge) i
    getArg (ElmEdge e _ ls) = getArg ls :. e
    getIdx (ElmEdge _ i _ ) = i
    getElm = id
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getElm #-}

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

-- | In case our sets have a @First@ boundary, then we always point from
-- the boundary "into" the set. Hence @SetNode == To@ and @NewNode ==
-- From@.
--
-- @{1,2,(3)} <- (4)@ yields @From 4 :. To 3@. Note the arrow direction @INTO@
-- the set.

instance EdgeFromTo First where
  edgeFromTo Proxy (SetBoundary to) (NewBoundary from) = From from :. To to
  {-# Inline edgeFromTo #-}

-- | And if the set has a @Last@ boundary, then we point from somewhere in
-- the set @To@ the @NewNode@, which is @Last@.
--
-- @{1,2,(3)} -> (4)@ yields @From 3 :. To 4@. Note the arrow direction @OUT
-- OF@ the set.

instance EdgeFromTo Last where
  edgeFromTo Proxy (SetBoundary from) (NewBoundary to) = From from :. To to
  {-# Inline edgeFromTo #-}

