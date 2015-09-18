
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



instance
  ( AddIndexDense a us is
  , GetIndex a (is:.BitSet I)
  , GetIx a (is:.BitSet I) ~ (BitSet I)
  ) => AddIndexDense a (us:.BitSet I) (is:.BitSet I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic rp) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk (S7 s a b y z y' z')
            | cm < csize = return $ Nothing
            | otherwise  = return $ Just (S8 s a b y z y' z' (mask :. k))
            where k  = (BitSet $ 2^cm-1)
                  cm = popCount mask - rp
                  mask = i `xor` l
                  l = getIndex a (Proxy :: Proxy (is:.BitSet I))
          step Nothing = return $ Done
          step (Just (S8 s a b y z y' z' (mask :. k)))
            | pk > popCount i - rp = return $ Done
            | otherwise            = let kk = popShiftL mask k
                                         aa = getIndex a (Proxy :: Proxy (is:.BitSet I))
                                     in  return $ Yield (S7 s a b (y:.kk) (z:.0) (y':.(kk.|.aa)) (z':.0)) (((S8 s a b y z y' z') . (mask :.)) <$> setSucc 0 (2^pk -1) k)
            where pk = popCount k
          csize = delay_inline minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo (cs:.c) (vs:.IVariable rp) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk (S7 s a b y z y' z')
            | c==EmptyOk  = return $ Just (S7 s a b y z y' z' :. mask :. cm :. 0)
            | cm == 0     = return $ Nothing
            | c==NonEmpty = return $ Just (S7 s a b y z y' z' :. mask :. cm :. 1)
            where mask = i `xor` l
                  cm   = popCount mask
                  l    = getIndex a (Proxy :: Proxy (is:.BitSet I))
          step Nothing = return $ Done
          step (Just (S7 s a b y z y' z' :. mask :. cm :. k))
            | popCount i < popCount (kk .|. l) + rp = return $ Done
            | otherwise = return $ Yield (S7 s a b (y:.kk) (z:.0) (y':.(kk.|.l)) (z':.0)) ((S7 s a b y z y' z' :. mask :. cm :.) <$> setSucc 0 (2^cm -1) k)
            where kk = popShiftL mask k
                  l  = getIndex a (Proxy :: Proxy (is:.BitSet I))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

