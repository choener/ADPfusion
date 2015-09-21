
module ADP.Fusion.Term.Edge.Set where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)
import Data.Bits.Ordered

import ADP.Fusion.Base
import ADP.Fusion.Term.Edge.Type



instance
  ( Monad m
  , Element    ls (BS2 First Last I)
  , MkStream m ls (BS2 First Last I)
  ) => MkStream m (ls :!: Edge e) (BS2 First Last I) where
  mkStream (ls :!: Edge f) (IStatic rp) u sij@(BS2 s i j)
    = flatten mk step $ mkStream ls (IStatic rpn) u tik
    where rpn | j >= 0    = rp
              | otherwise = rp+1
          tik | j >= 0    = BS2 (s `clearBit` (getIter j)) i undefi
              | otherwise = sij
          mk z
            | j >= 0 && popCount s >= 2 = return $ This z
            | j <  0 && popCount s >= 2 = return $ That (z,bits,maybeLsb bits)
            | popCount s <= max 1 rp    = return $ Naught
            | otherwise                 = error $ show ("Edge",s,i,j)
            where (BS2 zs _ zk) = getIdx z
                  bits        = s `xor` zs
          step Naught   = return Done
          step (This z)
            | popCount zs == 0 = return $ Done
            | otherwise = return $ Yield (ElmEdge (f (getIter zk) (getIter j)) sij undefbs2i z) Naught
            where (BS2 zs _ zk) = getIdx z
          step (That (z,bits,Nothing)) = return $ Done
          step (That (z,bits,Just j')) = let (BS2 zs _ (Iter zk)) = getIdx z
                                             tij'                 = BS2 (zs .|. bit j') (Iter zk) (Iter j')
                                         in  return $ Yield (ElmEdge (f zk j') tij' undefbs2i z) (That (z,bits,maybeNextActive j' bits))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls    (BS2 First Last O)
  , MkStream m ls (BS2 First Last O)
  ) => MkStream m (ls :!: Edge f) (BS2 First Last O) where
  mkStream (ls :!: Edge f) (OStatic ()) u sij
    = map undefined
    $ mkStream ls (undefined) u sij
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls    (BS2 First Last C)
  , MkStream m ls (BS2 First Last C)
  ) => MkStream m (ls :!: Edge f) (BS2 First Last C) where
  mkStream (ls :!: Edge f) Complemented u sij
    = map undefined
    $ mkStream ls Complemented u sij
  {-# Inline mkStream #-}

