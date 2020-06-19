
module ADPfusion.SynVar.Array.Set where

import Data.Bits
import Data.Bits.Extras
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map)
import Control.Applicative ((<$>))
import Data.Proxy

import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADPfusion.Base
import ADPfusion.SynVar.Array.Type
import ADPfusion.SynVar.Backtrack
import ADPfusion.SynVar.Indices



-- * Bitsets without any interfaces.

-- NOTE that we have to give as the filled index elements all bits that are
-- set in total, not just those we set right here. Otherwise the next
-- element will try a wrong set of indices.
--
-- NOTE even in the @IStatic@ case, we need to use flatten. If a node
-- requested a reserved bit, we need to free each reserved bit at least
-- once.

{-
instance
  ( Monad m
  , Element ls (BitSet I)
  , PrimArrayOps arr u x
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.BitSet I) (Z:.u) (Z:.BitSet I)
  , MkStream m ls (BitSet I)
  ) => MkStream m (ls :!: ITbl m arr u x) (BitSet I) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    -- TODO we need an additional parameter, @ii@ for what to index now,
    -- @jj@ (or so) for what to store as "complete index@.
    -- Right now, we go via this fun @aa@ hack. (Though maybe, we can do
    -- this always, anyway?)
    = map (\(s,ii,oo,ii',oo') -> let jj = ii' .|. aa
                                     aa = getIndex (Z:.getIdx s) (Proxy :: Proxy (Z:.BitSet I))
                                 in  ElmITbl (t!ii) jj oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
  {-# Inline mkStream #-}
-}


-- * Bitsets with two interfaces.
--
-- NOTE These are annoying to get right, if you also want to have good
-- performance.

instance
  ( Monad m
  , Element ls (BS2I I First Last)
  , PrimArrayOps arr (BS2I I First Last) x
  , MkStream m ls (BS2I I First Last)
  , Show x
  ) => MkStream m (ls :!: ITbl m arr (BS2I I First Last) x) (BS2I I First Last) where
  mkStream (ls :!: ITbl _ _ c t _) (IStatic rp) u sij@(s:>i:>j@(Iter jj))
    = flatten mk step $ mkStream ls (delay_inline IVariable rpn) u (delay_inline id $ tij)
          -- calculate new index. if we don't know the right-most interface
          -- anymore, than someone has taken it already. Also, if this
          -- synvar may be empty, do not modify the index. Otherwise, if
          -- @j@ is still known, remove it from the index set.
    where tij | jj == -1       = sij
              | c  == EmptyOk  = sij
              | c  == NonEmpty = s `clearBit` jj :> i :> Iter (-1)
          -- In case we do not know the rightmost interface, we instead
          -- increase the number of reserved bits.
          rpn | jj == -1
              && c == NonEmpty = rp+1
              | otherwise      = rp
          nec | c == NonEmpty = 1
              | c == EmptyOk  = 0
          mk z
            -- in case we have a non-empty synvar but not enough bits, we
            -- shall have nothing. We only need one extra mask bit, because
            -- @j@ is still known.
            | popCount mask < 1 && c == NonEmpty && j >= 0 = return $ Naught
            -- If @j@ is not known we need two bits to be non-empty.
            | popCount mask < 2 && c == NonEmpty && j <  0 = return $ Naught
            -- Not enough bits to reserve.
            | popCount mask - rp < 0                       = return $ Naught
            -- @j@ is still known, just create the sets ending in @j@
            | j >= 0                                       = return $ This (z,mask)
            -- @j@ is not known, we have a lot of work to do. Create the
            -- required @bits@ and prepare a @mask@ which will set the
            -- correct bits.
            | j <  0                                       = return $ That (z,mask,Just bits,maybeLsb bits)
            -- we somehow ended up with an improper state
            | otherwise                                    = error $ show (sij,mask,bits)
            where (zs:>_:>Iter zk) = getIdx z
                  mask             = s `xor` zs
                  bits             = BitSet $ 2 ^ (popCount mask - rp - nec) - 1
          step Naught          = return $ Done
          -- In case @j@ is known, we calculate the bits @msk@ that are not
          -- filled yet. We grab the previous right interface @zk@ and use
          -- it as the new left interface. We also use @j@ as the right
          -- interface. @ix@ holds everything that is now covered, withe
          -- the interface @i@ and @j@.
          step (This (z,mask)) = return $ Yield (ElmITbl (t!(msk:>k:>j)) ix undefbs2i z) Naught
            where (zs:>_:>zk) = getIdx z
                  k           = Iter $ getIter zk
                  ix          = (zs .|. msk) :> i :> j
                  msk         = if popCount mask == 0 then mask else mask `setBit` getIter k `setBit` jj
          -- whenever there is nothing more to do in the variable case.
          step (That (z,mask,Nothing,_)) = return $ Done
          -- We need to permute our population a bit. Once done, we grab
          -- the lowest significant bit.
          step (That (z,mask,Just bits,Nothing)) = return $ Skip (That (z,mask,nbts, maybeLsb =<< nbts))
            where nbts = popPermutation (popCount mask) bits
          -- The variable case.
          step (That (z,mask,Just bits,Just y))
            -- we do not have enough bits to be non-empty.
            |  popCount bb < 2 && c == NonEmpty
            -- our two interfaces are the same, but we are non-empty in
            -- which case this shouldn't happen.
            || getIter kk == getIter yy && c == NonEmpty
            -- our pop-count plus reserved count doesn't match up with the
            -- mask. We skip this as well.
            || popCount bb + rp /= popCount mask = return $ Skip (That (z,mask,Just bits, maybeNextActive y bits))
            -- finally, we can create the index for the current stuff
            -- @bb:>kk:>yy@ and prepare the full index, going from @i@ to
            -- @yy@, because someone grabbed @j@ already. Must have been
            -- an @Edge@ or s.th. similar.
            | otherwise = return $ Yield (ElmITbl (t!(bb:>kk:>yy)) ((zs .|. bb):>i:>yy) undefbs2i z)
                                                                 (That (z,mask,Just bits, maybeNextActive y bits))
            where (zs:>_:>zk) = getIdx z
                  kk          = Iter $ getIter zk
                  yy          = Iter . lsb $ popShiftL mask (bit y)
                  bb          = popShiftL mask bits `setBit` getIter kk `setBit` getIter yy
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

