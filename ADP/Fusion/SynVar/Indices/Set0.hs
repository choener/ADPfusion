
-- | @Set0@ provides index movement for sets with no interfaces.
--
-- TODO Sets with 1 and 2 interfaces will go into @Set1@ and @Set2@
-- modules.

module ADP.Fusion.SynVar.Indices.Set0 where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
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
  ( IndexHdr a us (BitSet I) cs c is (BitSet I)
  , MinSize c
  ) => AddIndexDense a (us:.BitSet I) (cs:.c) (is:.BitSet I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic rb) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
          -- @mk@ builds up the index we start with. First we ask in @l@
          -- for the index from the previous symbol. Then we calculate the
          -- @mask@, the bits we can still set. This is @i@ minus the @l@
          -- bits. Then we calculate the population count. For this we ask
          -- for the @popCount mask@ and lower it by the constraint @rb@
          -- (why?). Finally, we set exactly popCount bits in @k@. These
          -- @k@ bits are *not* the bits from the @mask@ but rather the
          -- lowest bits.
          -- @rb@ should be set by more-right symbols in case they need to
          -- reserve some bits but otherwise are static.
    where mk svS
            | cm < csize = return $ Nothing
            | otherwise  = return $ Just (svS :. mask :. k)
            where k  = (BitSet $ 2^cm-1)
                  cm = popCount mask - rb
                  mask = i `xor` l
                  RiBsI l = getIndex (sIx svS) (Proxy :: PRI is (BitSet I))
          step Nothing = return $ Done
          -- @step Just ...@ performs a non-trivial step. First we
          -- calculate the population count of the index for this symbol as
          -- @pk@. This will terminate once the popcount is higher than the
          -- index @i@ minus the reserved count @rb@.
          -- In case we don't terminate, we calculate the actual index @kk@
          -- by shifting the key @k@ around with our @mask@. The local
          -- index is given by @kk@, while the set of all active bits is
          -- @kk .|. aa@.
          --
          -- TODO is the stopping criterion actually right? Should'nd we
          -- look at all set bits? Also consider the comment above on @rb@.
          step (Just (svS@(SvS s a t y') :. mask :. k))
            | pk > popCount i - rb = return $ Done
            | otherwise            = let kk = popShiftL mask k
                                         RiBsI aa = getIndex a (Proxy :: PRI is (BitSet I))
                                     in  return $ Yield (SvS s a (t:.kk) (y' :.: RiBsI (kk.|.aa)))
                                                        ((svS :. mask :.) <$> setSucc 0 (2^pm -1) k)
            where pk = popCount k
                  pm = popCount mask
          !csize = minSize c  -- minimal set size via constraints
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo (cs:.c) (vs:.IVariable rb) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
          -- @mk@ builds up the initially set population. In case of
          -- @EmptyOk@ no bits are set. Otherwise we check first if we have
          -- bits left. If @cm==0@ then we immediately quit. If not, we
          -- activate one bit.
    where mk svS
            | csize==0  = return $ Just (svS :. mask :. cm :. csize)
            | cm == 0   = return $ Nothing
            | csize==1  = return $ Just (svS :. mask :. cm :. csize)
            where mask = i `xor` l
                  cm   = popCount mask
                  RiBsI l = getIndex (sIx svS) (Proxy :: PRI is (BitSet I))
                  csize = BitSet $ minSize c
          -- if the possible popcount in @i@ is less than the total
          -- popcount in @kk@ and @l@ and the reserved bits in @rb@, then
          -- we continue. This means returning @kk@ as the bitset for
          -- indexing; @kk.|.l@ as all set bits. @setSucc@ will rotate
          -- through all permutations for each popcount and mask.
          step Nothing = return $ Done
          step (Just (svS@(SvS s a t y') :. mask :. cm :. k))
            | popCount i < popCount (kk .|. l) + rb = return $ Done
            | otherwise = return $ Yield (SvS s a (t:.kk) (y' :.: RiBsI (kk.|.l)))
                                         ((svS :. mask :. cm :.) <$> setSucc 0 (2^cm -1) k)
            where kk = popShiftL mask k
                  RiBsI l  = getIndex a (Proxy :: PRI is (BitSet I))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- | Outside / Outside synvar indices are either @OStatic@ or @ORightOf@.
-- Of course, the single outside synvar is not to the right of itself, but
-- it is the final @RightOf@ object before we have the @FirstLeft@ object.

instance
  ( IndexHdr a us (BitSet O) cs c is (BitSet O)
  , MinSize c
  ) => AddIndexDense a (us:.BitSet O) (cs:.c) (is:.BitSet O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic rb) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
          -- We need to make the number of @0@s smaller, or make the number
          -- of @1@s larger. By an amount given by @rb@. 
    where mk svS
            -- not enough free bits with reserved count
            | rb + popCount bso >= popCount u = return $ Nothing
            | otherwise  = return $ Just (svS :. mask :. k)
            where RiBsO bsi bso = getIndex (sIx svS) (Proxy :: PRI is (BitSet O))
                  mask = u `xor` bso -- all bits available for permutations (upper bound, without already set bits)
                  k = BitSet $ 2 ^ rb - 1 -- the bits we want to trigger
          step Nothing = return $ Done
          -- | @step@ can now provide the outside index with @+rb@ more
          -- bits, while the inside index wont have those. The idea is that
          -- @outside@ provides the mask we can now plug additional
          -- @inside@ objects in -- but only in those plug-ports where @i@
          -- is zero.
          step (Just (svS@(SvS s a t y') :. mask :. k))
            -- drawing the next bitset ends up over the limit
            | pk > rb   = return $ Done
            | otherwise =
                let RiBsO bsi bso = getIndex a (Proxy :: PRI is (BitSet O))
                    kk = popShiftL mask k
                    tt = kk .|. bso -- the (smaller, more @1@ bits) lookup index
                in  return $ Yield (SvS s a (t:.tt) (y' :.: RiBsO bsi tt))
                                   ((svS :. mask :.) <$> setSucc 0 (2^rb -1) k)
            where pk = popCount k
          csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo (cs:.c) (vs:.ORightOf rb) (us:.u) (is:.i)
    = undefined
  {-# Inline addIndexDenseGo #-}

-- |

instance
  ( AddIndexDense a us cs is
  , GetIndex a (is:.BitSet O)
  , GetIx a (is:.BitSet O) ~ (BitSet O)
  ) => AddIndexDense a (us:.BitSet I) (cs:.c) (is:.BitSet O) where
--  addIndexDenseGo (cs:.c) (vs:.OFirstLeft rb) (us:.u) (is:.i)
--    = error "ping"
  {-# Inline addIndexDenseGo #-}

