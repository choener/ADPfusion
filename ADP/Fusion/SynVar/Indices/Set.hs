
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
    where mk svS
            | cm < csize = return $ Nothing
            | otherwise  = return $ Just (svS :. mask :. k)
            where k  = (BitSet $ 2^cm-1)
                  cm = popCount mask - rp
                  mask = i `xor` l
                  l = getIndex (sIx svS) (Proxy :: Proxy (is:.BitSet I))
          step Nothing = return $ Done
          step (Just (svS@(SvS s a b t y' z') :. mask :. k))
            | pk > popCount i - rp = return $ Done
            | otherwise            = let kk = popShiftL mask k
                                         aa = getIndex a (Proxy :: Proxy (is:.BitSet I))
                                     in  return $ Yield (SvS s a b (t:.kk) (y':.(kk.|.aa)) (z':.0))
                                                        ((svS :. mask :.) <$> setSucc 0 (2^pk -1) k)
            where pk = popCount k
          csize = delay_inline minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo (cs:.c) (vs:.IVariable rp) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS
            | c==EmptyOk  = return $ Just (svS :. mask :. cm :. 0)
            | cm == 0     = return $ Nothing
            | c==NonEmpty = return $ Just (svS :. mask :. cm :. 1)
            where mask = i `xor` l
                  cm   = popCount mask
                  l    = getIndex (sIx svS) (Proxy :: Proxy (is:.BitSet I))
          step Nothing = return $ Done
          step (Just (svS@(SvS s a b t y' z') :. mask :. cm :. k))
            | popCount i < popCount (kk .|. l) + rp = return $ Done
            | otherwise = return $ Yield (SvS s a b (t:.kk) (y':.(kk.|.l)) (z':.0))
                                         ((svS :. mask :. cm :.) <$> setSucc 0 (2^cm -1) k)
            where kk = popShiftL mask k
                  l  = getIndex a (Proxy :: Proxy (is:.BitSet I))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- * Bitsets with a single boundary.
--
-- TODO write (copy ...) code



-- * Bitsetts with two boundaries, a first, and a last element.
--
-- TODO write me

instance
  (
  ) => AddIndexDense (cs:.c) (us:.BS2 First Last I) (is:.BS2 First Last I) where

