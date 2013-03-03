{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Region where

import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq
import qualified Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Stream.Size
import Control.Exception (assert)

import ADP.Fusion.Classes



data Region e = Region !(VU.Vector e)



-- * Instances for 1-dimensional region terminal.

instance MkElm x i => MkElm (x:.Region e) i where
  newtype Plm (x:.Region e) i = Pregion (Elm x i :. Is i :. Is i)
  newtype Elm (x:.Region e) i = Eregion (Elm x i :. Is i :. VU.Vector e)
  type    Arg (x:.Region e) = Arg x :. (VU.Vector e)
  topIdx (Eregion (_ :. k :. _)) = k
  getArg (Eregion (x :. _ :. t)) = getArg x :. t
  {-# INLINE topIdx #-}
  {-# INLINE getArg #-}

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



-- * Instances for k-dimensional region terminal

instance Next x y => Next (x:.Region Int) (y:.(Int:.Int)) where
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

