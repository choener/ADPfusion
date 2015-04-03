
module ADP.Fusion.SynVar.Array.Set where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Data.Vector.Fusion.Stream.Monadic
import Prelude hiding (map)
import Data.Bits
import Data.Bits.Extras
import Data.Bits.Ordered

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack



-- NOTE that we have to give as the filled index elements all bits that are
-- set in total, not just those we set right here. Otherwise the next
-- element will try a wrong set of indices.
--
-- NOTE even in the @IStatic@ case, we need to use flatten. If a node
-- requested a reserved bit, we need to free each reserved bit at least
-- once.

instance
  ( Monad m
  , Element ls BitSet
  , PrimArrayOps arr BitSet x
  , MkStream m ls BitSet
  ) => MkStream m (ls :!: ITbl m arr BitSet x) BitSet where
  mkStream (ls :!: ITbl c t _) (IStatic rp) u s
    = flatten mk step Unknown $ mkStream ls (delay_inline IVariable $ rp - csize) u s
    where mk z
            | cm < csize = return (z , mask , Nothing)
            | otherwise  = return (z , mask , Just k )
            where k  = (BitSet $ 2^cm-1)
                  cm = popCount mask - rp
                  mask = s `xor` (getIdx z)
          step (_,_,Nothing) = return $ Done
          step (z,mask,Just k)
            | pk > popCount s - rp = return $ Done
            | otherwise            = let kk = movePopulation mask k
                                     in  return $ Yield (ElmITbl (t!kk) (kk .|. getIdx z) (BitSet 0) z) (z,mask,setSucc (BitSet 0) (2^pk -1) k)
            where pk = popCount k
          !csize | c==EmptyOk  = 0
                 | c==NonEmpty = 1
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  mkStream (ls :!: ITbl c t _) (IVariable rp) u s
    = flatten mk step Unknown $ mkStream ls (IVariable rp) u s
    where mk z
            | c==EmptyOk  = return (z , mask , cm , Just 0 )
            | cm == 0     = return (z , mask , cm , Nothing) -- we are non-empty but have no free bits left
            | c==NonEmpty = return (z , mask , cm , Just 1 )
            where mask = s `xor` (getIdx z) -- bits that are still free
                  cm   = popCount mask
          step (z,mask,cm,Nothing) = return $ Done
          step (z,mask,cm,Just k )
            | popCount s < popCount (kk .|. getIdx z) + rp = return $ Done
            | otherwise = return $ Yield (ElmITbl (t!kk) (kk .|. getIdx z) (BitSet 0) z) (z,mask,cm,setSucc (BitSet 0) (2^cm -1) k)
            where kk = movePopulation mask k
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}



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

