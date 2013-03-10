{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}

module ADP.Fusion.Term where

import Data.Array.Repa.Index
import Control.DeepSeq
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Data.Vector.Fusion.Stream.Size

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Classes
import ADP.Fusion.Region
import ADP.Fusion.None
import ADP.Fusion.Chr
import ADP.Fusion.Peek

import Debug.Trace



data Term ts = Term ts
data T = T



instance Build (Term ts)

instance
  ( StreamElm x i
  ) => StreamElm (x:.Term ts) i where
  data Elm (x:.Term ts) i = ElmTerm !(Elm x i :. IxP i :. E (Term ts))
  type Arg (x:.Term ts)   = Arg x :. E (Term ts)
  getIxP (ElmTerm (_:.k:._)) = k
  getArg (ElmTerm (x:.k:.t)) = getArg x :. t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

instance (Monad m, TermElement m ts i) => Element m (Term ts) i where
  type E (Term ts) = TermElm ts
  getE (Term ts) l r = getSimple ts l r
  {-# INLINE getE #-}

instance
  ( Monad m
  ) => TermElement m T Z where
  type TermElm T = Z
  getSimple T (IxPz _) (IxPz _) = return Z
  {-# INLINE getSimple #-}

instance
  ( Monad m
  , TermElement m ts is
  , Element m (Chr e) i
  ) => TermElement m (ts:.Chr e) (is:.i) where
  type TermElm   (ts:.Chr e)         = TermElm ts :. e
  getSimple (ts:.Chr e) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    = do es <- getSimple ts ls rs
         e  <- getE (Chr e) l r
         return $ es:.e
  {-# INLINE getSimple #-}

instance
  ( Monad m
  , TermElement m ts is
  , Element m (Peek e) i
  ) => TermElement m (ts:.Peek e) (is:.i) where
  type TermElm (ts:.Peek e) = TermElm ts :. e
  getSimple (ts:.Peek d ve) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    = do es <- getSimple ts ls rs
         e  <- getE (Peek d ve) l r
         return $ es :. e

instance
  ( Monad m
  , TermElement m ts i
  , MkStream m ss i, Next (Term ts) i, StreamElm ss i
  , Index i
--  , Show i, Show (IxP i), Show (IxT i), Show (Elm ss i)
  ) => MkStream m (ss:.Term ts) i where
  mkStream !(ss:.t@(Term ts)) !ox !ix = S.flatten mk step Unknown $ mkStream ss ox' ix' where
    (ox',ix') = convT t ox ix
    mk !y = do
      let l = getIxP y
      let r = initP t ox ix l
      -- traceShow ("mk",ox,ix,l,r,y) $
      return (y:.l:.r)
    step !(y:.l:.r)
      | doneP t ox ix r = {- traceShow ("step-done ",ix,ox,l,r,y) $ -} return $ S.Done
      | otherwise       = do let r' = nextP t ox ix l r
                             e <- getE t l r
                             -- traceShow ("step-yield",ix,ox,l,r,y) $
                             return $ S.Yield (ElmTerm (y:.r:.e)) (y:.l:.r')
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance (Next (Term ts) is, Next t i) => Next (Term (ts:.t)) (is:.i) where
  initP (Term (ts:.t)) (IxTmt (os:.o)) (is:.i) (IxPmt (ls:.l))
    = IxPmt $ initP (Term ts) os is ls :. initP t o i l
  doneP (Term (ts:.t)) (IxTmt (os:.o)) (is:.i) (IxPmt (rs:.r))
    = doneP (Term ts) os is rs || doneP t o i r
  convT (Term (ts:.t)) (IxTmt (os:.o)) (is:.i) =
    let (os',is') = convT (Term ts) os is
        (o' ,i' ) = convT t o i
    in  (IxTmt (os':.o'), is':.i')
  nextP (Term (ts:.t)) (IxTmt (os:.o)) (is:.i) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    -- next step gets us out of uppermost bounds, so advance next inner
    | doneP t o i r' = IxPmt $ nextP (Term ts) os is ls rs :. initP t o i l
    | otherwise      = IxPmt $ rs :. nextP t o i l r
    where r' = nextP t o i l r
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

instance Next (Term T) Z where
  initP _ _ _ _ = IxPz True
  doneP _ _ _ (IxPz b) = not b
  convT _ _ ix  = (IxTz, ix)
  nextP (Term T) IxTz Z (IxPz _) (IxPz _) = IxPz False
  {-# INLINE convT #-}
  {-# INLINE initP #-}
  {-# INLINE doneP #-}
  {-# INLINE nextP #-}

instance NFData T
