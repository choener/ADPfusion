
module ADP.Fusion.Term.Edge
  ( module ADP.Fusion.Term.Edge.Type
  , module ADP.Fusion.Term.Edge.Set
  ) where

import ADP.Fusion.Term.Edge.Set
import ADP.Fusion.Term.Edge.Type



{-
-- | An edge terminal returns the pair of indices forming the edge.

data Edge e where
  Edge  :: !(Int -> Int -> e) -> Edge e

edge = (,)
{-# Inline edge #-}

instance Build (Edge i)

instance
  (Element ls i
  ) => Element (ls :!: Edge e) i where
    data Elm (ls :!: Edge e) i = ElmEdge !e !i !(Elm ls i)
    type Arg (ls :!: Edge e)   = Arg ls :. e
    getArg (ElmEdge e _ ls) = getArg ls :. e
    getIdx (ElmEdge _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

instance
  ( Monad m
  , Element ls (BitSet:>Interface First:>Interface Last)
  , MkStream m ls (BitSet:>Interface First:>Interface Last)
  ) => MkStream m (ls :!: Edge e) (BitSet:>Interface First:>Interface Last) where
    -- encodes in the first index arg, what the previously set @Last@ was
    mkStream (ls :!: Edge f) Static s@(BitSet zb:>Interface zi:>Interface zj) (BitSet b:>Interface i:>Interface j)
      -- if we have @popCount b == 1@, then this is an initial node,
      -- creating the first node. Otherwise the edge just extends an
      -- existing node.
      -- TODO need to figure out this "first node" stuff here
      = S.map (\z -> let (BitSet zb:>_:>Interface zj) = getIdx z
                     in  ElmEdge (f zj j) (BitSet b:>Interface i:>Interface j) z
              )
      $ mkStream ls (Variable Check (Just (popCount b -1) )) s (BitSet (clearBit b j):>Interface i:>Interface j)
    -- in the variable case, the @Last@ point is unset and may move freely.
    -- @First@ is still fixed. In @k@, we have the number of bits from
    -- @BitSet b@ that we should set! The bit we set is also the @Last@
    -- interface bit.
    mkStream (ls :!: Edge f) (Variable Check (Just k)) s@(BitSet zb:>Interface zi:>Interface zj) c@(BitSet b:>Interface i:>_)
      = S.flatten mk step Unknown
      $ mkStream ls (Variable Check (Just $ k-1)) s c
      where mk z = let (BitSet z':>_:>_) = getIdx z ; a = b `xor` z' in return (z,a,lsbActive a)
            step (z,a,lsbA)
              | lsbA < 0  = return $ S.Done
              | otherwise = return $ S.Yield (ElmEdge (f cj lsbA) (BitSet (cs .|. bit lsbA):>Interface ci:>Interface lsbA) z) (z,a,nextActive lsbA a)
              where (BitSet cs:>Interface ci:>Interface cj) = getIdx z
            {-# Inline [0] mk   #-}
            {-# Inline [0] step #-}
    {-# Inline mkStream #-}
-}

