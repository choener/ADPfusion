
module ADP.Fusion.SynVar.Array.Set where

import Data.Bits
import Data.Bits.Extras
import Data.Bits.Ordered
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack



-- * Bitsets without any interfaces.

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



-- * Bitsets with two interfaces.

instance
  ( Monad m
  , Element ls (BS2I First Last)
  , PrimArrayOps arr (BS2I First Last) x
  , MkStream m ls (BS2I First Last)
  ) => MkStream m (ls :!: ITbl m arr (BS2I First Last) x) (BS2I First Last) where
  mkStream (ls :!: ITbl c t _) (IStatic rp) u sij@(s:>i:>j@(Iter jj))
    = flatten mk step Unknown $ mkStream ls (delay_inline IVariable rpn) u (delay_inline id $ tij)
    where tij | jj == -1       = sij
              | c  == EmptyOk  = sij
              | c  == NonEmpty = s `clearBit` jj :> i :> Iter (-1)
          rpn | jj == -1
              && c == NonEmpty = rp+1
              | otherwise      = rp
          mk z
            | popCount bits < 1 && c == NonEmpty = return $ Naught
            | j >= 0                             = return $ This (z,bits,Just zk)
            | j < 0                              = return $ That (z,bits,bk)
            | otherwise = error $ show ("e",sij)
            where (zs:>_:>Iter zk) = getIdx z
                  bits             = s `xor` zs
                  bk | popCount bits == 0 = Just 0
                     | popCount bits == 1 = Just zk
                     | otherwise          = maybeLsb bits
          step Naught = return Done
          step (This (z,bits,Just k')) = let (zs:>_:>_) = getIdx z ; k = Iter k'
                                         in  return $ Yield (ElmITbl (t!(bits:>k:>j)) ((zs .|. bits):>i:>j) undefbs2i z) Naught
          step (That (z,bits,Nothing)) = return $ Done
          step (That (z,bits,Just l')) = let (zs:>_:>Iter zk') = getIdx z ; zk = Iter zk' ; l = Iter l'
                                         in  return $ Yield (ElmITbl (t!(bits:>zk:>l)) ((zs .|. bits):>i:>l) undefbs2i z) (That (z,bits,succActive l' bits))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}










{-  
    = flatten mk step Unknown $ mkStream ls (delay_inline IVariable rpn) u (delay_inline id $ tij)
    where mk z | j >= 0 && c == EmptyOk = return $ This (z,zk,bits)
               | j <  0 && c == EmptyOk = return $ That (z,Iter zk,Just (bits:>Iter (lsbActive bits)))
               | c == NonEmpty && popCount bits == 0 = return $ Naught
               | otherwise = error $ show ("X ",sij,zs,zk)
               where (zs:>_:>Iter zk) = getIdx z
                     bits                  = s `xor` zs
          -- in case @Interface Last@ is still fixed
          step (This  (z,k,bits)) = return $ Yield (ElmITbl (t!(bits:>k:>j)) sij undefbs2i z) Naught
          -- in case @Interface Last@ is already variable
          step (That (z,k,Nothing        )) = return $ Done
          step (That (z,k,Just (bits:>j'))) = return $ Yield (ElmITbl (t!(bits:>Iter k:>j'))
                                                              (s:>i:>j') undefbs2i z) (That (z,k,setSucc (bits:>j') (bits:>j') (bits:>j')))
          -- we have nothing left to do
          step Naught = return Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          tij | jj == -1       = sij
              | c  == EmptyOk  = sij
              | c  == NonEmpty = s `clearBit` jj :> i :> Iter (-1)
          rpn | jj == -1
              && c == NonEmpty = rp+1
              | otherwise      = rp
  mkStream (ls :!: ITbl c t _) (IVariable rp) u sij@(s:>i:>j)
    = flatten mk step Unknown $ mkStream ls (delay_inline IVariable rpn) u sij
    where mk z
            | c == EmptyOk  = return (z, mask `clearBit` zk, Just (0:>Iter 0))
            | c == NonEmpty = return (z, mask `clearBit` zk, Just (1:>Iter 0))
            where (zs:>_:>Iter zk) = getIdx z
                  mask                  = s `xor` zs
          step (z,mask,Nothing      ) = return $ Done
          step (z,mask,Just (ys:>yl))
            | cm == 0   = return $ Yield (ElmITbl (t!(0:>0:>0)) (zs:>i:>Iter zki) undefbs2i z) (z,mask,Nothing)
            | otherwise = return $ Yield (ElmITbl (t!(ys':>zk:>yl)) ((zs .&. ys):>i:>yl) undefbs2i z)
                                                   (z,mask,setSucc (0:>Iter 0) (2^(cm-1)-1:>Iter 0) (ys:>yl))
            where (zs:>_:>Iter zki) = getIdx z
                  zk                     = Iter zki
                  cm                     = popCount mask
                  ys'                    = movePopulation mask ys .|. BitSet zki
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          rpn | c == NonEmpty = rp+1
              | c == EmptyOk  = rp
  {-# Inline mkStream #-}
-}

