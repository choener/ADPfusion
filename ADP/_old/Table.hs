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
import Data.Array.Repa.Index.Point
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
  !EmptyOk   -- ^ allow empty table, that is return result for subword (i,i) ?
  !es    -- ^ data

data EmptyOk
  = Enone -- all dimensions are to be non-empty
  | Esome -- some, but not all, dimensions may be empty (you can /NOT/ select which one may be empty currently)
  | Eall  -- all dimensions may be empty
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
  data Elm (x:.MTable (PA.MutArr m arr)) i = ElmMTable !(Elm x i :. IxP i :. E (MTable (PA.MutArr m arr)))
  type Arg (x:.MTable (PA.MutArr m arr))   = Arg x :. E (MTable (PA.MutArr m arr))
  getIxP (ElmMTable (_:.k:._)) = k
  getArg (ElmMTable (x:.k:.t)) = getArg x :. t
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

instance
  ( Monad m
  , Next (MTable (PA.MutArr m arr)) (is:.i)
  , Element m (MTable (PA.MutArr m arr)) (is:.i)
  , StreamElm ss (is:.i)
  , MkStream m ss (is:.i)
  ) => MkStream m (ss:.MTable (PA.MutArr m arr)) (is:.i) where
  mkStream !(ss:.mtbl) !ox !ix = S.flatten mk step Unknown $ mkStream ss ox' ix' where
    (ox',ix') = convT mtbl ox ix
    mk !y = do let l = getIxP y
               let r = initP mtbl ox ix l
               return (y:.l:.r)
    step !(y:.l:.r)
      | doneP mtbl ox ix r = return $ S.Done
      | otherwise          = do let r' = nextP mtbl ox ix l r
                                e <- getE mtbl l r
                                return $ S.Yield (ElmMTable (y:.r:.e)) (y:.l:.r')
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , PA.Sh arr ~ (is:.i)
  , PA.MC arr
  , PA.MPAO m arr
  , Shape (is:.i)
  , Index is, Index i
  ) => Element m (MTable (PA.MutArr m arr)) (is:.i) where
  type E (MTable (PA.MutArr m arr)) = PA.E arr
  getE (MTable _ es) l r = PA.readM es $ from l r  --(Z:. Subword (l:.r)) 
  {-# INLINE getE #-}

instance
  (Next Fake is, Next Fake i
  ) => Next (MTable es) (is:.i) where
  -- TODO how does "Tmany" look like in higher-dimensional space?
  convT (MTable ne _) (IxTmt (ts:.t)) (is:.i)
    = let (as,bs) = convT (Fake ne) ts is
          (a,b)   = convT (Fake ne) t  i
      in (IxTmt $ as:.a, bs:.b)
  initP (MTable ne _) (IxTmt (ts:.t)) (is:.i) (IxPmt (ls:.l))
    = let rs = initP (Fake ne) ts is ls
          r  = initP (Fake ne) t  i  l
      in  IxPmt $ rs:.r
  doneP (MTable ne _) ts is rs -- (IxTmt (ts:.t)) (is:.i) (IxPmt (rs:.r))
    = doneP (Fake ne) ts is rs
  nextP (MTable ne _) (IxTmt (os:.o)) (is:.i) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    -- next step gets us out of uppermost bounds, so advance next inner
    | doneP (Fake ne) o i r' = IxPmt $ nextP (Fake ne) os is ls rs :. initP (Fake ne) o i l
    | otherwise              = IxPmt $ rs :. nextP (Fake ne) o i l r
    where r' = nextP (Fake ne) o i l r
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

data Fake = Fake !EmptyOk

instance Next Fake Subword where
  convT (Fake eok) _ ix@(Subword (i:.j))
    | eok == Eall  = (IxTsubword Inner, ix)
    | eok == Enone = (IxTsubword Inner, subword i (j-1))
  -- TODO fix initP !
  initP (Fake ne) (IxTsubword oir) (Subword (i:.j)) (IxPsubword l)
    | oir == Outer = IxPsubword j
    | otherwise    = IxPsubword l
  doneP (Fake ne) (IxTsubword _) (Subword (i:.j)) (IxPsubword r) = r>j
  nextP (Fake ne) (IxTsubword oir) (Subword (i:.j)) (IxPsubword l) (IxPsubword r)
    = IxPsubword $ r+1
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

instance Next Fake Point where
  convT (Fake eok) _ (Point j)
    | eok == Eall  = (IxTpoint Inner, Point j)
    | eok == Enone = (IxTpoint Inner, Point $ j-1)
  initP (Fake eok) (IxTpoint oir) (Point j) (IxPpoint l)
    | oir == Outer = IxPpoint j
    | otherwise    = IxPpoint l
  doneP (Fake eok) (IxTpoint _) (Point j) (IxPpoint r) = r>j || j<0 || r<0
  nextP (Fake eok) (IxTpoint _) (Point j) (IxPpoint l) (IxPpoint r)
    = IxPpoint $ r+1
--  nextP (Fake ne) IxTz Z (IxPz l) (IxPz r) = IxPz False
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

instance Next Fake Z where
  convT (Fake ne) _ Z = (IxTz,Z)
  initP (Fake ne) _ Z (IxPz b) = IxPz b
  doneP (Fake ne) IxTz Z (IxPz b) = not b
  nextP (Fake ne) IxTz Z (IxPz l) (IxPz r) = IxPz False
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

instance (Next Fake is, Next Fake i) => Next Fake (is:.i) where
  convT (Fake ne) (IxTmt (ts:.t)) (is:.i)
    | True = let (as,bs) = convT (Fake ne) ts is
                 (a,b)   = convT (Fake ne) t  i
             in (IxTmt $ as:.a, bs:.b)
  doneP (Fake ne) (IxTmt (ts:.t)) (is:.i) (IxPmt (rs:.r))
    = doneP (Fake ne) ts is rs
  initP (Fake ne) (IxTmt (ts:.t)) (is:.i) (IxPmt (ls:.l))
    = let rs = initP (Fake ne) ts is ls
          r  = initP (Fake ne) t  i  l
      in  IxPmt $ rs:.r
  nextP (Fake ne) (IxTmt (os:.o)) (is:.i) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    -- next step gets us out of uppermost bounds, so advance next inner
    | doneP (Fake ne) o i r' = IxPmt $ nextP (Fake ne) os is ls rs :. initP (Fake ne) o i l
    | otherwise              = IxPmt $ rs :. nextP (Fake ne) o i l r
    where r' = nextP (Fake ne) o i l r
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

instance (NFData (Elm x i), NFData (IxP i), NFData (PA.E arr)) => NFData (Elm (x:.MTable (PA.MutArr m arr)) i) where
  rnf (ElmMTable (a:.b:.c)) = rnf a `seq` rnf b `seq` rnf c

instance (NFData x, NFData arr) => NFData (x:.MTable arr) where
  rnf (x:.MTable b arr) = rnf x `seq` rnf b `seq` rnf arr

instance NFData EmptyOk where
  rnf (!x) = ()

instance Next (MTable es) Subword where
  initP (MTable ne _) (IxTsubword oir) (Subword (i:.j)) (IxPsubword l)
    | i>j          = IxPsubword $ j+1
    | oir == Outer = IxPsubword $ j
    | ne == Enone  = IxPsubword $ l+1
    | otherwise    = IxPsubword $ l
  nextP (MTable ne _) (IxTsubword oir) (Subword (_:.j)) (IxPsubword l) (IxPsubword r)
    | otherwise    = IxPsubword $ r+1
  convT (MTable ne _) _ ix@(Subword (i:.j))
    | ne == Eall  = (IxTsubword Inner, ix)
    | otherwise   = (IxTsubword Inner, subword i (j-1))
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}

instance Build (MTable e)

instance NFData (PA.MutArr m arr) where
  rnf (!x) = ()

