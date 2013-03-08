{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Empty where

import Control.DeepSeq
import Control.Exception (assert)
import Data.Array.Repa.Index
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Classes



-- | 

data Empty = Empty

instance NFData Empty where
  rnf Empty = ()

instance
  ( Monad m
  ) => Element m Empty Subword where
  type E Empty = ()
  getE Empty (IxPsubword l) (IxPsubword r) = assert (l==r && l>=0) $ return ()
  {-# INLINE getE #-}

instance
  ( StreamElm x i
  ) => StreamElm (x:.Empty) i where
  data Elm (x:.Empty) i = ElmEmpty (Elm x i :. IxP i :. E Empty)
  type Arg (x:.Empty)   = Arg x :. E Empty
  getIxP (ElmEmpty (_:.k:._)) = k
  getArg (ElmEmpty (x:.k:.t)) = getArg x :. t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

-- |
--
-- TODO this instance is currently "dangerous". When standing alone in a
-- production rule, it will always return a result. We should make this
-- foolproof, maybe?

instance
  ( StreamElm ss Subword
  , MkStream m ss Subword
  ) => MkStream m (ss:.Empty) Subword where
  mkStreamO (ss:.c) ox ix = S.mapM step $ mkStreamO ss ox' ix' where
    (ox',ix') = convT c ox ix
    step y = do
      let l = getIxP y
      let r = toR ix
      e <- getE c l r
      return (ElmEmpty (y:.r:.e))
    {-# INLINE step #-}
  {-# INLINE mkStreamO #-}
  {-
  mkStreamI (ss:.c) ox ix = S.mapM step $ mkStreamI ss ox' ix' where
    (ox',ix') = convT c ox ix
    step y = do
      let l = getIxP y
      let r = case ox of
                IxTsubword Outer -> toR ix
                _                -> nextP c ox ix l l
      e <- getE c l r
      return $ ElmEmpty (y:.r:.e)
    {-# INLINE step #-}
  {-# INLINE mkStreamI #-}
-}
  mkStream = mkStreamO
  {-# INLINE mkStream #-}

instance Next Empty Subword where
  initP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k)
    | otherwise = undefined
  nextP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k) (IxPsubword l)
    | oir == Outer = IxPsubword $ j+1
    | otherwise    = IxPsubword $ l+1
  convT _ ox@(IxTsubword oir) ix@(Subword (i:.j))
    | oir == Outer = (IxTsubword Outer, Subword (i:.j))
    | otherwise    = (ox, ix)
  {-# INLINE nextP #-}
  {-# INLINE convT #-}

instance NFData x => NFData (x:.Empty) where
  rnf (x:.Empty) = rnf x

instance (NFData x) => NFData (Elm (x:.Empty) Subword) where

instance Build Empty




