{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Region where

import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq

import ADP.Fusion.Classes



data Region e = Region !(VU.Vector e)

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



-- ** NFData instances

instance NFData (Z:.VU.Vector e)

