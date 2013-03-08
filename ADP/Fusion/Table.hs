{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyDataDecls #-}

module ADP.Fusion.Table where

import Control.DeepSeq
import Control.Exception (assert)
import Data.Array.Repa.Index
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Data.Array.Repa.Shape

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA

import ADP.Fusion.Classes

import Debug.Trace



-- | Mutable tables for memoization.
--
-- TODO Switch to an encoding using fully adaptive arrays. Cf. Manuel
-- Chakravarty's work (implemented in dph).
--
-- TODO empty / non-empty stuff !

data MTable es = MTable
  !TNE   -- ^ allow empty table, that is return result for subword (i,i) ?
  !es    -- ^ data

data TNE
  = Tmany -- 0+
  | Tsome -- 1+
  deriving (Eq,Ord,Show)

instance (NFData es) => NFData (MTable es) where
  rnf (MTable b es) = b `seq` rnf es

instance
  ( Monad m
  , PA.MPAO m arr, PA.Sh arr ~ (Z:.Subword), PA.MC arr
  ) => Element m (MTable (PA.MutArr m arr)) Subword where
  type E (MTable (PA.MutArr m arr)) = PA.E arr
  getE (MTable _ es) (IxPsubword l) (IxPsubword r) = PA.readM es (Z:. Subword (l:.r)) 
  {-# INLINE getE #-}

instance
  ( StreamElm x i
  ) => StreamElm (x:.MTable (PA.MutArr m arr)) i where
  data Elm (x:.MTable (PA.MutArr m arr)) i = ElmMTable (Elm x i :. IxP i :. E (MTable (PA.MutArr m arr)))
  type Arg (x:.MTable (PA.MutArr m arr))   = Arg x :. E (MTable (PA.MutArr m arr))
  getIxP (ElmMTable (_:.k:._)) = k
  getArg (ElmMTable (x:.k:.t)) = let a = getArg x in a:.t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

instance
  ( Monad m
  , PA.MPAO m arr, PA.Sh arr ~ (Z:.Subword), PA.MC arr
  , NFData (PA.E arr), NFData (Elm ss Subword)
  , Next (MTable (PA.MutArr m arr)) Subword
  , StreamElm ss Subword
  , MkStream m ss Subword
  , Show (PA.E arr)
  ) => MkStream m (ss:.MTable (PA.MutArr m arr)) Subword where
  mkStreamO (ss:.mtbl) ox@(IxTsubword Outer) ix = S.mapM step $ mkStreamI ss ox' ix' where
    (ox',ix') = convT mtbl ox ix
    step y = do
      let l = getIxP y
      let r = toR ix
      e <- getE mtbl l r
      return (ElmMTable (y:.r:.e))
    {-# INLINE step #-}
  {-# INLINE mkStreamO #-}
  mkStreamI (ss:.mtbl) ox ix = S.flatten mk step Unknown $ mkStreamI ss ox' ix' where
    (ox',ix') = convT mtbl ox ix
    mk y = do let l = getIxP y
              let r = initP mtbl ox ix l
              return (y:.l:.r)
    step (y:.l:.r)
      | r `leftOfR` ix = do let r' = nextP mtbl ox ix l r
                            e <- getE mtbl l r
                            return $ S.Yield (ElmMTable (y:.r:.e)) (y:.l:.r')
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamI #-}
  mkStream = mkStreamO
  {-# INLINE mkStream #-}

instance (NFData (Elm x i), NFData (IxP i), NFData (PA.E arr)) => NFData (Elm (x:.MTable (PA.MutArr m arr)) i) where
  rnf (ElmMTable (a:.b:.c)) = rnf a `seq` rnf b `seq` rnf c

instance (NFData x, NFData arr) => NFData (x:.MTable arr) where
  rnf (x:.MTable b arr) = rnf x `seq` rnf b `seq` rnf arr

instance NFData TNE where
  rnf (!x) = ()

instance Next (MTable es) Subword where
  initP (MTable ne _) (IxTsubword oir) (Subword (i:.j)) (IxPsubword l)
    | i>j          = IxPsubword $ j+1
    | oir == Outer = IxPsubword $ j
    | ne == Tsome  = IxPsubword $ l+1
    | otherwise    = IxPsubword $ l
  nextP (MTable ne _) (IxTsubword oir) (Subword (_:.j)) (IxPsubword l) (IxPsubword r)
    | otherwise    = IxPsubword $ r+1
  convT (MTable ne _) _ ix@(Subword (i:.j))
    | ne == Tmany = (IxTsubword Inner, ix)
    | otherwise   = (IxTsubword Inner, subword i (j-1))
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}

instance Build (MTable e)

instance NFData (PA.MutArr m arr) where
  rnf (!x) = ()

