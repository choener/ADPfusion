{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Chr where

import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq
import qualified Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Stream.Size
import Control.Exception (assert)

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Point

import ADP.Fusion.Classes

import Debug.Trace



-- | Terminal parser for a single character.

data Chr e = Chr !(VU.Vector e)

instance NFData (Chr e) where
  rnf (Chr ve) = rnf ve

instance
  ( Monad m
  , VU.Unbox e
  ) => Element m (Chr e) Subword where
  type E (Chr e) = e
  getE (Chr ve) (IxPsubword l) (IxPsubword r) =
    let e = VU.unsafeIndex ve l
    in  assert (l<=r && l>=0 && VU.length ve > r) $ return e
  {-# INLINE getE #-}

instance
  ( Monad m
  , VU.Unbox e
  ) => Element m (Chr e) Point where
  type E (Chr e) = e
  getE (Chr ve) (IxPpoint l) (IxPpoint r) = assert (l<=r && l>=0 && VU.length ve > r) $ return $ VU.unsafeIndex ve l

instance
  ( StreamElm x i
  ) => StreamElm (x:.Chr e) i where
  data Elm (x:.Chr e) i = ElmChr (Elm x i :. IxP i :. E (Chr e))
  type Arg (x:.Chr e)   = Arg x :. E (Chr e)
  getIxP (ElmChr (_:.k:._)) = k
  getArg (ElmChr (x:.k:.t)) = getArg x :. t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

-- |
--
-- TODO this instance is currently "dangerous". When standing alone in a
-- production rule, it will always return a result. We should make this
-- foolproof, maybe?

instance
  ( VU.Unbox e, NFData e
  , StreamElm ss Subword
  , MkStream m ss Subword
  ) => MkStream m (ss:.Chr e) Subword where
  mkStreamO (ss:.c) ox@(IxTsubword Outer) ix = S.mapM step $ mkStreamO ss ox' ix' where
    (ox',ix') = convT c ox ix
    step y = do
      let l = getIxP y
      let r = toR ix
      e <- getE c l r
      return (ElmChr (y:.r:.e))
    {-# INLINE step #-}
  {-# INLINE mkStreamO #-}
  mkStreamI (ss:.c) ox ix = S.flatten mk step Unknown $ mkStreamI ss ox' ix' where
    (ox',ix') = convT c ox ix
    mk y = do let l = getIxP y
              let r = initP c ox ix l
              return (y:.l:.r)
    step (y:.l:.r)
      | r `leftOfR` ix = do let r' = nextP c ox ix l r
                            e <- getE c l r
                            return $ S.Yield (ElmChr (y:.r:.e)) (y:.l:.r')
      | otherwise       = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamI #-}
  mkStream = mkStreamO
  {-# INLINE mkStream #-}

instance
  ( VU.Unbox e, NFData e, StreamElm ss Point, MkStream m ss Point
  ) => MkStream m (ss:.Chr e) Point where
  mkStreamO (ss:.c) ox@(IxTpoint Outer) ix = S.mapM step $ mkStreamO ss ox' ix' where
    (ox',ix') = convT c ox ix
    step y = do
      let l = getIxP y
      let r = toR ix
      e <- getE c l r
      return (ElmChr (y:.r:.e))
    {-# INLINE step #-}
  {-# INLINE mkStreamO #-}
  mkStream = mkStreamO
  {-# INLINE mkStream #-}

instance Next (Chr e) Subword where
  initP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k)
    | oir == Outer && k+1 ==j = IxPsubword $ j    -- rightmost position, (i,i+1) parse
    | oir == Outer            = IxPsubword $ j+1  -- wrong size of region
    | otherwise = IxPsubword $ k+1                -- normal, inner behaviour
  nextP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k) (IxPsubword l)
    | otherwise    = {- traceShow ("next",i,j,k,l) $ -} IxPsubword $ j+1 -- TODO is this correct ?
  convT _ ox@(IxTsubword oir) ix@(Subword (i:.j)) = (ox, Subword (i:.j-1))
    {-
    | oir == Outer = (IxTsubword Outer, Subword (i:.j-1))
    | otherwise    = (ox, Subword (i:.j-1))
    -}
  doneP (Chr e) (IxTsubword oir) (Subword (i:.j)) (IxPsubword r)
    = {- traceShow ("done",oir,i,j,r) $ -} r>j
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}
  {-# INLINE doneP #-}

instance Next (Chr e) Point where
  initP _ (IxTpoint oir) (Point j) (IxPpoint l)
    | oir == Outer && l+1 == j = IxPpoint $ j
    | oir == Outer             = IxPpoint $ j+1
    | otherwise                = IxPpoint $ l
  nextP _ (IxTpoint oir) (Point j) (IxPpoint l) (IxPpoint r)
    = IxPpoint $ j+1 -- TODO is this correct ?
  convT _ ox (Point k) = (ox, Point $ k-1)
  -- TODO check j<0 needed?
  doneP _ _ (Point j) (IxPpoint r)
    = r>j || j<0
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}
  {-# INLINE doneP #-}

instance NFData x => NFData (x:.Chr e) where
  rnf (x:.Chr ve) = rnf x `seq` rnf ve

instance (NFData x, VU.Unbox e) => NFData (Elm (x:.Chr e) Subword) where

instance Build (Chr e)

