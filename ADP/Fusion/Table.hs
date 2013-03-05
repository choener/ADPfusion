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
  !Bool   -- ^ allow empty table, that is return result for subword (i,i) ?
  !es     -- ^ data

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
  , Next (MTable (PA.MutArr m arr)) Subword
  , StreamElm ss Subword
  , MkStream m ss Subword
  , Show (PA.E arr)
  ) => MkStream m (ss:.MTable (PA.MutArr m arr)) Subword where
  mkStream (ss:.mtbl) ox ix = S.flatten mk step Unknown $ mkStream ss ox' ix where
    (ox',_) = convT mtbl ox ix
    mk y
      | (IxTsubword Outer) <- ox = return (y:.l:.r)
      | otherwise                = return (y:.l:.l)
      where l = getIxP y
            r = toR    ix
    step (y:.l:.r)
      | r `leftOfR` ix = do let r' = nextP mtbl ox ix l r
                            e <- getE mtbl l r
                            {- traceShow (l,r,e) $ -}
                            return $ S.Yield (ElmMTable (y:.r:.e)) (y:.l:.r')
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance Next (MTable es) Subword where
  nextP _ (IxTsubword oir) (Subword (_:.j)) (IxPsubword _) (IxPsubword l)
    | oir == Outer = IxPsubword $ j+1
    | otherwise    = IxPsubword $ l+1
  convT _ _ ix = (IxTsubword Inner, ix)
  {-# INLINE nextP #-}
  {-# INLINE convT #-}

