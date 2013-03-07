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

import ADP.Fusion.Classes



-- | Terminal parser for a single character.

data Chr e = Chr !(VU.Vector e)

instance NFData (Chr e) where
  rnf (Chr ve) = rnf ve

instance
  ( Monad m
  , NFData e
  , VU.Unbox e
  ) => Element m (Chr e) Subword where
  type E (Chr e) = e
  getE (Chr ve) (IxPsubword l) (IxPsubword r) =
    let e = VU.unsafeIndex ve l
    in  {- (ve,l,r,e) `deepseq` -} assert (l<=r && l>=0 && VU.length ve > r) $ return e
  {-# INLINE getE #-}

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
  mkStream (ss:.c) ox ix = {- (c,ox,ix,ox',ix') `deepseq` -} S.flatten mk step Unknown $ mkStream ss ox' ix' where
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
  {-# INLINE mkStream #-}

instance Next (Chr e) Subword where
  initP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k)
    | oir == Outer && k+1 ==j = IxPsubword $ j    -- rightmost position, (i,i+1) parse
    | oir == Outer            = IxPsubword $ j+1  -- wrong size of region
    | otherwise = IxPsubword $ k+1                -- normal, inner behaviour
  nextP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k) (IxPsubword l)
    | otherwise    = IxPsubword $ j+1
  convT _ ox@(IxTsubword oir) ix@(Subword (i:.j))
    | oir == Outer = (IxTsubword Outer, Subword (i:.j-1))
    | otherwise    = (ox, Subword (i:.j-1))
  {-# INLINE nextP #-}
  {-# INLINE convT #-}

instance NFData x => NFData (x:.Chr e) where
  rnf (x:.Chr ve) = rnf x `seq` rnf ve

instance (NFData x, VU.Unbox e) => NFData (Elm (x:.Chr e) Subword) where

instance Build (Chr e)

