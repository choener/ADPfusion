{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Peek where

import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq
import qualified Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Stream.Size
import Control.Exception (assert)

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Point

import ADP.Fusion.Classes



-- | Works like the Chr, but will not advance the indices AND returns a default
-- element in case the parser were to ask for an impossible element.

data Peek e = Peek !e !(VU.Vector e)

instance NFData (Peek e) where
  rnf (Peek e ve) = e `seq` rnf ve

{-
instance
  ( Monad m
  , VU.Unbox e
  ) => Element m (Peek e) Subword where
  type E (Peek e) = e
  getE (Peek d ve) (IxPsubword l) (IxPsubword r) =
    let e = VU.unsafeIndex ve l
    in  if (l<=r && l>=0 && VU.length ve > r)
        then $ return e
        else $ return d
  {-# INLINE getE #-}
-}

instance
  ( Monad m
  , VU.Unbox e
  ) => Element m (Peek e) Point where
  type E (Peek e) = e
  getE (Peek d ve) (IxPpoint l) (IxPpoint r) =
    if (l<=r && l>0 && VU.length ve > r)
    then return $ VU.unsafeIndex ve (l-1)
    else return $ d

instance
  ( StreamElm x i
  ) => StreamElm (x:.Peek e) i where
  data Elm (x:.Peek e) i = ElmPeek (Elm x i :. IxP i :. E (Peek e))
  type Arg (x:.Peek e)   = Arg x :. E (Peek e)
  getIxP (ElmPeek (_:.k:._)) = k
  getArg (ElmPeek (x:.k:.t)) = getArg x :. t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

-- |

{-
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
-}

-- | We can simplify the stream functions as we always return an element,
-- though it sometimes is the default element.

instance
  ( VU.Unbox e, NFData e
  , StreamElm ss Point
  , MkStream m ss Point
  ) => MkStream m (ss:.Peek e) Point where
  mkStreamO (ss:.pk) ox@(IxTpoint Outer) ix = S.mapM step $ mkStreamO ss ox ix where
    step y = do
       let l = getIxP y
       let r = toR ix
       e <- getE pk l r
       return (ElmPeek (y:.r:.e))
    {-# INLINE step #-}
  {-# INLINE mkStreamO #-}

{-
instance Next (Chr e) Subword where
  initP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k)
    | oir == Outer && k+1 ==j = IxPsubword $ j    -- rightmost position, (i,i+1) parse
    | oir == Outer            = IxPsubword $ j+1  -- wrong size of region
    | otherwise = IxPsubword $ k+1                -- normal, inner behaviour
  nextP _ (IxTsubword oir) (Subword (i:.j)) (IxPsubword k) (IxPsubword l)
    | otherwise    = IxPsubword $ j+1 -- TODO is this correct ?
  convT _ ox@(IxTsubword oir) ix@(Subword (i:.j)) = (ox, Subword (i:.j-1))
    {-
    | oir == Outer = (IxTsubword Outer, Subword (i:.j-1))
    | otherwise    = (ox, Subword (i:.j-1))
    -}
  doneP (Chr e) (IxTsubword oir) (Subword (i:.j)) (IxPsubword r)
    = r>j
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}
  {-# INLINE doneP #-}
-}

instance Next (Peek e) Point where
  initP _ (IxTpoint oir) (Point j) (IxPpoint l)
--    | oir == Outer && l+1 == j = IxPpoint $ j
--    | oir == Outer             = IxPpoint $ j+1
    | otherwise                = IxPpoint $ l
  nextP _ (IxTpoint oir) (Point j) (IxPpoint l) (IxPpoint r)
    = IxPpoint $ j+1 -- TODO is this correct ?
  convT _ ox (Point k) = (ox, Point $ k)
  -- TODO check j<0 needed?
  doneP _ _ (Point j) (IxPpoint r)
    = r>j || j<0
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}
  {-# INLINE doneP #-}

instance NFData x => NFData (x:.Peek e) where
  rnf (x:.Peek d ve) = rnf x `seq` d `seq` rnf ve

{-
instance (NFData x, VU.Unbox e) => NFData (Elm (x:.Peek e) Subword) where
-}

instance Build (Peek e)

