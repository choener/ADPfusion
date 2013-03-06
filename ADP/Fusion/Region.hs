{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Region where

import Control.DeepSeq
import Control.Exception (assert)
import Data.Array.Repa.Index
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Classes

import Debug.Trace



data Region e = Region
  !(Maybe Int)      -- ^ minimal size
  !(Maybe Int)      -- ^ maximal size
  !(VU.Vector e)    -- ^ actual  data

instance NFData (Region e) where
  rnf (Region a b ve) = {- rnf a `seq` rnf b `seq` -} rnf ve

-- * Instances for 1-dimensional region terminal.

-- |

instance (Monad m, VU.Unbox e) => Element m (Region e) Subword where
  type E (Region e) = VU.Vector e
  getE (Region _ _ ve) (IxPsubword l) (IxPsubword r) =
    let
      e = VU.unsafeSlice l (r-l) ve
    in  {- (ve,l,r,e) `deepseq` -} assert (l<=r && l>=0 && VU.length ve > r) $ return e
  {-# INLINE getE #-}

-- |

instance
  ( StreamElm x i
  , NFData (Arg x)
  ) => StreamElm (x:.Region e) i where
  data Elm (x:.Region e) i  = ElmRegion (Elm x i :. IxP i :. E (Region e))
  type Arg (x:.Region e)    = Arg x :. E (Region e)
  getIxP (ElmRegion (_:.k:._)) = k
  getArg (ElmRegion (x:.k:.t)) = let a = getArg x in {- a `deepseq` -} a :. t
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

-- | The subword instance allows us to use 'Region's in typical context-free
-- grammars with CYK-style parsing.

instance
  ( Monad m, NFData (IxP Subword), NFData (E (Region e)), VU.Unbox e, NFData (Elm ss Subword), NFData (Region e)
  , MkStream m ss Subword, StreamElm ss Subword
  , Next (Region e) Subword, Index Subword
--  , Show (Elm ss Subword), Show e
  ) => MkStream m (ss:.Region e) Subword where
  mkStream (ss:.reg) ox ix = (reg,ox,ix,ox') `deepseq` S.flatten mk step Unknown $ mkStream ss ox' ix where
    (ox',_) = convT reg ox ix
    mk y
--      | (IxTsubword Outer) <- ox = return (y:.l:.r)
      | otherwise                = return (y:.l:.r)
      where l = getIxP y -- this is the left boundary of the current symbol
            r = initP reg ox ix (getIxP y) -- the right boundary depends on certain conditions checked in Next
    step (y:.l:.r)
      | r `leftOfR` ix = do let r' = nextP reg ox ix l r
                            e <- getE reg l r
                            return $ S.Yield (ElmRegion (y:.r:.e)) (y:.l:.r')
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

-- |
--
-- TODO interplay of 'oir' and non-empty regions

instance Next (Region e) Subword where
  initP (Region mi _ _) (IxTsubword oir) (Subword (i:.j)) (IxPsubword k)
    | i>j          = IxPsubword $ j+1
    | oir == Outer = IxPsubword $ j
    | Just z <- mi = IxPsubword $ k+z
    | otherwise    = IxPsubword $ k
  nextP (Region _ ma _) (IxTsubword oir) (Subword (i:.j)) (IxPsubword k) (IxPsubword l)
    | oir == Outer = IxPsubword $ j+1
    | Just z <- ma
    , l-k>z        = IxPsubword $ j+1
    | otherwise    = IxPsubword $ l+1
  convT _ _ ix = (IxTsubword Inner, ix)
  {-# INLINE initP #-}
  {-# INLINE nextP #-}
  {-# INLINE convT #-}

instance Build (Region e)

deriving instance (Show (Elm x Subword), Show e,VU.Unbox e) => Show (Elm (x:.Region e) Subword)

instance NFData x => NFData (x:.Region e) where
  rnf (x:.Region a b ve) = {- (a,b) `deepseq` -} rnf x `seq` rnf ve

instance (NFData x, VU.Unbox e) => NFData (Elm (x:.Region e) Subword) where

{-
instance ( Monad m, Index i, NFData (Is i)
         , MkS m ss i, MkElm ss i
         , MkElm (ss:.Region e) i
         , Next (Region e) i
         , TEE m (Region e) i
         ) => MkS m (ss:.Region e) i where
  mkS (ss:.re) ox ix = S.flatten mk step Unknown $ mkS ss (convT re ox) ix where
    mk y = let k = topIdx y in k `deepseq` return (y:.k:.k)
    step (y:.l:.r)
      | r `leftOfR` ix = do let r' = suc re ox ix l r
                            e <- tiOne re l r
                            (r',e) `deepseq` return $ S.Yield (Eregion (y:.r:.e)) (y:.l:.r')
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkS #-}

-- | For each new index type (like 'Z:.(Int:.Int)') we need a 'Next' instance.
-- 'Term'-based instances use a small "z" instead of the big "Z".

instance (VU.Unbox e) => Next (Region e) (Z:.(Int:.Int)) where
  suc (Region e) (IsTii (t:.oir)) (ix:.(i:.j)) (IsIntInt (ks:.k)) (IsIntInt (ls:.l))
    | oir == Outer = IsIntInt (IsZ False :. j+1) -- if we are 'Outer' do only one step, then terminate
    | l > j        = IsIntInt (IsZ False :. j+1)
    -- ASSERT below fires if input too small
    | otherwise    = assert (VU.length e > j) $ IsIntInt (ls :. l+1) -- otherwise step by one
  convT _ (IsTii (t:.oir)) = IsTii (t :. Inner)
  {-# INLINE suc #-}
  {-# INLINE convT #-}

-- | The element extraction instance can be incomplete as 1-dim regions return
-- only one element.

instance (Monad m, VU.Unbox e) => TEE m (Region e) (y:.(Int:.Int)) where
  type TE (Region e) = VU.Vector e
  newtype TI (Region e) (y:.(Int:.Int)) m = TIregionNotImplemented ()
  tiOne (Region ve) (IsIntInt (_:.l)) (IsIntInt (_:.r)) = return $ VU.unsafeSlice l (r-l) ve
  te = error "not implemented"
  ti = error "not implemented"
  tisuc = error "not implemented"
  tifin = error "not implemented"
  tiget = error "not implemented"
  {-# INLINE tiOne #-}



-- * Instances for k-dimensional region terminal

instance (Index y, Next x y) => Next (x:.Region Int) (y:.(Int:.Int)) where
  suc (x:.r) (IsTii (os:.o)) (ix:.(i:.j)) (IsIntInt (ks':.k')) (IsIntInt (z:.k))
    | o == Outer = let inner = suc x os ix ks' z
                   in  if inner `leftOfR` ix
                       then IsIntInt $ inner :. k
                       else IsIntInt $ inner :. k'
    | k<j = IsIntInt $ z :. k+1
    | otherwise = IsIntInt $ suc x os ix ks' z :. k'
  convT (x:.r) (IsTii (t:.oir))
--    | oir == Outer = IsTii (t:.Inner)
    | otherwise    = IsTii (convT x t:.Inner)
  {-# INLINE suc #-}
  {-# INLINE convT #-}



-- * NFData instances

instance NFData (Z:.VU.Vector e)

-}

