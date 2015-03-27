
module ADP.Fusion.SynVar.Array.Set where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Data.Vector.Fusion.Stream.Monadic
import Prelude hiding (map)
import Data.Bits
import Data.Bits.Ordered

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack


{-
instance
  ( Monad m
  , PrimArrayOps arr (BS2I First Last) x
  , Element    ls (BS2I First Last)
  , MkStream m ls (BS2I First Last)
  ) => MkStream m (ls :!: ITbl m arr (BS2I First Last) x) (BS2I First Last) where
  mkStream (ls :!: ITbl c t _) IStatic u sij@(s:>i:>j)
    -- (@vik@ is already filled, we fill the difference to @sij@ with @wkj@ and
    -- set as the new "combined" index @sij@ (this is the static case, so it is
    -- indeed @sij@.
    = map (\z -> let (v:>_:>Interface k) = getIdx z
                     w = s `xor` v
                     wkj = (w:>Interface k:>j)
                 in  ElmITbl (t!wkj) (s:>i:>j) undefbs2i z)
    $ mkStream ls IVariable u sij
  mkStream (ls :!: ITbl c t _) IVariable u sij@(s:>i:>k)
    = flatten mk step Unknown
    $ mkStream ls IVariable u sij
    where mk z = let (v:>_:>k) = getIdx z
                     ful       = (s `xor` v)
                     lsba      = lsbActive ful
                     initial   = (BitSet lsba :> Interface lsba)
                 in  return (z :. ful :. Just initial)
          step (z :. ful :. Just (w:>l) )
            = let (_:>_:>k) = getIdx z
              in  return $ Yield (ElmITbl (t!(w:>k:.l)) undefined undefined undefined) undefined
          step (_ :. _   :. Nothing )
            = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}
-}

