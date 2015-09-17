
module ADP.Fusion.Term.Epsilon.Set where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Epsilon.Type



instance
  ( Monad m
  , MkStream m ls (BS2I I First Last)
  ) => MkStream m (ls :!: Epsilon) (BS2I I First Last) where
  mkStream (ls :!: Epsilon) (IStatic r) u s@(bs:>_:>_)
    = staticCheck (bs==0)
    . map (ElmEpsilon s s)
    $ mkStream ls (IStatic r) u s
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m ls (BS2I O First Last)
  ) => MkStream m (ls :!: Epsilon) (BS2I O First Last) where
  mkStream (ls :!: Epsilon) (OStatic r) u@(us:>_:>_) s@(bs:>_:>_)
    = staticCheck (us==bs)
    . map (ElmEpsilon s s)
    $ mkStream ls (OStatic r) u s
  {-# Inline mkStream #-}

