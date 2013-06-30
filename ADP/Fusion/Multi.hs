{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | The multi-tape extension of ADPfusion. Just re-exports everything.

module ADP.Fusion.Multi
  ( module ADP.Fusion.Multi.Classes
  , module ADP.Fusion.Multi.Empty
  , module ADP.Fusion.Multi.GChr
  , module ADP.Fusion.Multi.None
  ) where

import ADP.Fusion.Multi.Classes
import ADP.Fusion.Multi.None
import ADP.Fusion.Multi.GChr
import ADP.Fusion.Multi.Empty



{-
type instance TermOf (Term ts (ZeroOne r xs)) = TermOf ts :. Maybe r

instance
  ( TermValidIndex ts is
  ) => TermValidIndex (Term ts (ZeroOne r xs)) (is:.PointL) where
  termDimensionsValid (ts:!ZeroOne (gchr)) = termDimensionsValid (ts:!gchr)
  {-
  getTermParserRange (ts:!
  -}




-- The experimental zero/one wrapper

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts (ZeroOne r xs)) (is:.PointL) where
  termStream (ts:!(ZeroOne (GChr f xs))) (io:.o) (is:.ij@(PointL(i:.j)))
    = doubleStream
    . termStream (ts:!GChr f xs) (io:.o) (is:.ij)
    where
      {-# INLINE doubleStream #-}
      doubleStream (S.Stream step sS n) = S.Stream sNew (Left sS) (2*n) where
        {-# INLINE [1] sNew #-}
        sNew (Left s) = do r <- step s
                           case r of
                             S.Yield (abc:!:(es:.e)) s' -> return $ S.Yield (abc:!:(es:.Just e)) (Right s')
                             S.Skip                  s' -> return $ S.Skip                       (Left  s')
                             S.Done                     -> return $ S.Done
        sNew (Right s) = do r <- step s
                            case r of
                              S.Yield (abc:!:(es:.e)) s' -> return $ S.Yield (abc:!:(es:.Nothing)) (Left s')
--                              S.Skip                  s' -> return $ S.Skip                        (Left s')
--                              S.Done                     -> return $ S.Done
  {-# INLINE termStream #-}
-}


-- Empty

