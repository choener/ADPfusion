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

import Debug.Trace



data Term ts = Term ts
data T = T



instance Build (Term ts)

instance
  ( StreamElm x i
  ) => StreamElm (x:.Term ts) i where
  data Elm (x:.Term ts) i = ElmTerm (Elm x i :. IxP i :. E (Term ts))
  type Arg (x:.Term ts)   = Arg x :. E (Term ts)
  getIxP (ElmTerm (_:.k:._)) = k
  getArg (ElmTerm (x:.k:.t)) = getArg x :. t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

instance (Monad m, TermElement m ts i) => Element m (Term ts) i where
  type E (Term ts) = TermElm ts
  getE (Term ts) l r = getSimple ts l r

instance
  ( Monad m
  ) => TermElement m T Z where
  type TermElm T = Z
  getSimple T (IxPz _) (IxPz _) = return Z

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

instance
  ( Monad m
  , TermElement m ts i
  , MkStream m ss i, Next (Term ts) i, StreamElm ss i
  , Index i
  ) => MkStream m (ss:.Term ts) i where
  mkStream (ss:.t@(Term ts)) ox ix = S.flatten mk step Unknown $ mkStream ss ox' ix' where
    (ox',ix') = convT t ox ix
    mk y = do let l = getIxP y
              let r = initP t ox ix l
              return (y:.l:.r)
    step (y:.l:.r)
      | doneP t ox ix r = return $ S.Done
      | otherwise       = do let r' = nextP t ox ix l r
                             e <- getE t l r
                             return $ S.Yield (ElmTerm (y:.r:.e)) (y:.l:.r')
    {-
    step (y:.l:.r)
      | r `leftOfR` ix = do let r' = nextP t ox ix l r
                            e <- getE t l r
                            return $ S.Yield (ElmMTable (y:.r:.e)) (y:.l:.r')
      | otherwise = return $ S.Done
-}


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
    {-
    | doneP t o i r = IxPmt $ nextP (Term ts) os is ls rs :. initP t o i l
    | otherwise     = IxPmt $ rs :. nextP t o i l r
    -}
    where r' = nextP t o i l r

instance Next (Term T) Z where
  initP _ _ _ _ = IxPz True
  doneP _ _ _ (IxPz b) = not b
  convT _ _ ix  = (IxTz, ix)
  nextP (Term T) IxTz Z (IxPz _) (IxPz _) = IxPz False














{-

-- |
--
-- TODO 'MkStream' for multidimensional terms always uses the 'flatten' method
-- for now. Doing the faster 'mapM' version is very complicated and requires
-- specialized instances.

  {-
  mkStreamO (ss:.t@(Term ts)) ox ix = S.mapM step $ mkStreamI ss ox' ix' where
    (ox',ix') = convT t ox ix
    step y = do
      let l = getIxP y
      let r = initP t ox ix (getIxP y)
      e <- getSimple ts l r
      return (ElmTerm (y:.r:.e))
    {-# INLINE step #-}
    -}
  {-
  mkStreamO (ss:.t@(Term ts)) ox ix = S.flatten mkT stepT Unknown $ S.mapM step $ mkStreamI ss ox' ix' where
    (ox',ix') = convT t ox ix
    mkT (y:.l:.r) = do k <- initTI ts l r
                       return (y:.l:.r:.k)
    stepT (y:.l:.r:.k)
      | doneTI k = return $ S.Done -- TODO stepped through all term possibilities
      | otherwise = do
          k' <- nextTI ts l r k
          e <- getTI ts l r k
          return $ S.Yield (ElmTerm (y:.r:.e)) (y:.l:.r:.k')
    step y = return (y:.l:.r) where
      l = getIxP y
      r = initP t ox ix (getIxP y)
    {-# INLINE mkT #-}
    {-# INLINE stepT #-}
    {-# INLINE step #-}
    -}
  {-
    mk y = return (y:.l:.r) where
      l = getIxP y
      r = initP t ox ix (getIxP y)
    step (y:.l:.r)
      | r `leftOfR` ix = 
    -}
  {-# INLINE mkStreamO #-}
  mkStreamI = mkStreamO
  {-# INLINE mkStreamI #-}


  getSimple _ _ _ = return Z
  {-
  data TermIx m T Z = TIxZ Bool
  initTI T IxPz IxPz = return $ TIxZ True
  doneTI (TIxZ b) = not b
  getTI T IxPz IxPz _ = return Z
  nextTI _ _ _ _ = return $ TIxZ False
  -}

{-
  getSimple (ts:.c) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    = do es <- getSimple ts ls rs
         e  <- getE c l r
         return (es:.e) -}
  {-
  data TermIx  m (ts:.Chr e) (is:.i) = TIxChr (TermIx m ts is)
  initTI (ts:.Chr ve) (IxPmt (ls:.l)) (IxPmt (rs:.r))
    = do xs <- initTI ts ls rs
         return $ TIxChr xs
  doneTI (TIxChr ks) = doneTI ks
  getTI (ts:.c) (IxPmt (ls:.l)) (IxPmt (rs:.r)) (TIxChr ks)
    = do es <- getTI ts ls rs ks
         e <-  getE c l r
         return (es:.e)
  nextTI _ _ _ _ =
  -}

instance (Next (Term ts) is) => Next (Term (ts:.t)) (is:.Subword) where
{-
  convT (Term (ts:.t)) (IxTmt (os:.o)) (is:.i) =
    let
      (tsT,isI) = convT (Term ts) os is
      (tT, iI ) = convT t o i
    in (IxTmt (tsT:.tT), isI :. iI)
  initP (Term (ts:.t)) (IxTmt (js:.j)) (is:.i) (IxPmt (ls:.l)) =
    let
      as = initP (Term ts) js is ls
      a  = initP t j i l
    in  IxPmt (as:.a)
-}

{-
instance
  ( Index is, Index i
  ) => Index (is:.i) where
  data IxP (is:.i) = IxPmt (IxP is :. IxP i)
  data IxT (is:.i) = IxTmt (IxT is :. IxT i)
  toL (is:.i) = IxPmt (toL is :. toL i)
  initT = IxTmt (initT :. initT)
-}

instance Next (Term T) Z where
--  {-# INLINE suc #-}
--  {-# INLINE convT #-}

instance NFData (IxP Z) where

instance NFData (IxP (is:.i)) where

deriving instance Show (IxT Z)
-}
