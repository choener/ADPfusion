
module ADP.Fusion.Edge.Set where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Stream.Size
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)
import Data.Bits.Ordered

import ADP.Fusion.Base
import ADP.Fusion.Edge.Type



{-
instance
  ( Monad m
  , Element    ls (BS1I Last)
  , MkStream m ls (BS1I Last)
  ) => MkStream m (ls :!: Edge e) (BS2I Last) where
-}

instance
  ( Monad m
  , Element    ls (BS2I First Last)
  , MkStream m ls (BS2I First Last)
  ) => MkStream m (ls :!: Edge e) (BS2I First Last) where
  mkStream (ls :!: Edge f) IStatic u sij@(s:>i:>Interface j)
    = map (\z -> let (_:>_:>Interface k) = getIdx z
                 in  ElmEdge (f k j) (s:>Interface k:>Interface j) undefbs2i z)
    $ mkStream ls IStatic u ((s `clearBit` j):>i:>undefi)
  mkStream (ls :!: Edge f) IVariable u sij@(s:>i:>_)
    = flatten mk step Unknown
    $ mkStream ls IVariable u sij
    where mk z = let (t:>_:>_) = getIdx z; u = s `xor` t in return (z :. u :. lsbActive u)
          step (z :. u :. l)
            | l == (-1) = return $ Done
            | otherwise = do let (t:>_:>Interface k) = getIdx z
                             let tkl = (t `setBit` l :> Interface k :> Interface l)
                             return $ Yield (ElmEdge (f k l) tkl undefbs2i z) (z:.u:.nextActive l u)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls    (Outside (BS2I First Last))
  , MkStream m ls (Outside (BS2I First Last))
  ) => MkStream m (ls :!: Edge f) (Outside (BS2I First Last)) where
  mkStream (ls :!: Edge f) (OStatic ()) u sij
    = map undefined
    $ mkStream ls (undefined) u sij
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls    (Complement (BS2I First Last))
  , MkStream m ls (Complement (BS2I First Last))
  ) => MkStream m (ls :!: Edge f) (Complement (BS2I First Last)) where
  mkStream (ls :!: Edge f) Complemented u sij
    = map undefined
    $ mkStream ls Complemented u sij
  {-# Inline mkStream #-}


undefbs2i :: BS2I f l
undefbs2i = BitSet (-1) :> Interface (-1) :> Interface (-1)
{-# Inline undefbs2i #-}

undefi :: Interface i
undefi = Interface (-1)
{-# Inline undefi #-}

{-
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

