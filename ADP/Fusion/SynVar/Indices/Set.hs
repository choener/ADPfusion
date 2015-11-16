
module ADP.Fusion.SynVar.Indices.Set where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)
import Data.Bits.Extras
import Data.Bits

import Data.PrimitiveArray hiding (map)
import Data.Bits.Ordered

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



-- * Bitsets without any boundaries
--
-- TODO outside and complement code

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.BitSet I)
  , GetIx a (is:.BitSet I) ~ (BitSet I)
  ) => AddIndexDense a (us:.BitSet I) (is:.BitSet I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic rp) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
          -- @mk@ builds up the index we start with. First we ask in @l@
          -- for the index from the previous symbol. Then we calculate the
          -- @mask@, the bits we can still set. This is @i@ minus the @l@
          -- bits. Then we calculate the population count. For this we ask
          -- for the @popCount mask@ and lower it by the constraint @rp@
          -- (why?). Finally, we set exactly popCount bits in @k@. These
          -- @k@ bits are *not* the bits from the @mask@ but rather the
          -- lowest bits.
          -- @rp@ should be set by more-right symbols in case they need to
          -- reserve some bits but otherwise are static.
    where mk svS
            | cm < csize = return $ Nothing
            | otherwise  = return $ Just (svS :. mask :. k)
            where k  = (BitSet $ 2^cm-1)
                  cm = popCount mask - rp
                  mask = i `xor` l
                  l = getIndex (sIx svS) (Proxy :: Proxy (is:.BitSet I))
          step Nothing = return $ Done
          -- @step Just ...@ performs a non-trivial step. First we
          -- calculate the population count of the index for this symbol as
          -- @pk@. This will terminate once the popcount is higher than the
          -- index @i@ minus the reserved count @rp@.
          -- In case we don't terminate, we calculate the actual index @kk@
          -- by shifting the key @k@ around with our @mask@. The local
          -- index is given by @kk@, while the set of all active bits is
          -- @kk .|. aa@.
          --
          -- TODO is the stopping criterion actually right? Should'nd we
          -- look at all set bits? Also consider the comment above on @rp@.
          step (Just (svS@(SvS s a b t y' z') :. mask :. k))
            | pk > popCount i - rp = return $ Done
            | otherwise            = let kk = popShiftL mask k
                                         aa = getIndex a (Proxy :: Proxy (is:.BitSet I))
                                     in  return $ Yield (SvS s a b (t:.kk) (y':.(kk.|.aa)) (z':.0))
                                                        ((svS :. mask :.) <$> setSucc 0 (2^pk -1) k)
            where pk = popCount k
          csize = delay_inline minSize c  -- minimal set size via constraints
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo (cs:.c) (vs:.IVariable rp) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
          -- @mk@ builds up the initially set population. In case of
          -- @EmptyOk@ no bits are set. Otherwise we check first if we have
          -- bits left. If @cm==0@ then we immediately quit. If not, we
          -- activate one bit.
    where mk svS
            | c==EmptyOk  = return $ Just (svS :. mask :. cm :. 0)
            | cm == 0     = return $ Nothing
            | c==NonEmpty = return $ Just (svS :. mask :. cm :. 1)
            where mask = i `xor` l
                  cm   = popCount mask
                  l    = getIndex (sIx svS) (Proxy :: Proxy (is:.BitSet I))
          step Nothing = return $ Done
          -- if the possible popcount in @i@ is less than the total
          -- popcount in @kk@ and @l@ and the reserved bits in @rp@, then
          -- we continue. This means returning @kk@ as the bitset for
          -- indexing; @kk.|.l@ as all set bits. @setSucc@ will rotate
          -- through all permutations for each popcount and mask.
          step (Just (svS@(SvS s a b t y' z') :. mask :. cm :. k))
            | popCount i < popCount (kk .|. l) + rp = return $ Done
            | otherwise = return $ Yield (SvS s a b (t:.kk) (y':.(kk.|.l)) (z':.0))
                                         ((svS :. mask :. cm :.) <$> setSucc 0 (2^cm -1) k)
            where kk = popShiftL mask k
                  l  = getIndex a (Proxy :: Proxy (is:.BitSet I))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.BitSet O)
  , GetIx a (is:.BitSet O) ~ (BitSet O)
  ) => AddIndexDense a (us:.BitSet O) (is:.BitSet O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic rp) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS
            | undefined = return $ Nothing
            | otherwise = return $ Just (svS :. mask :. k)
            where
          step = undefined
          csize = delay_inline minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- * Bitsets with a single boundary.
--
-- TODO write (copy ...) code



-- * Bitsets with two boundaries, a first, and a last element.
--
-- TODO write me

instance
  (
  ) => AddIndexDense (cs:.c) (us:.BS2 First Last I) (is:.BS2 First Last I) where

