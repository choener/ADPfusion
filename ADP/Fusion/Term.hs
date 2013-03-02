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

import ADP.Fusion.Classes
import ADP.Fusion.Region
import ADP.Fusion.None



data Term ts = Term ts
data T = T

instance (Monad m) => TEE m T Z where
  type TE T = Z
  newtype TI T Z m = TIZ Bool
  te T _ _ = S.singleton Z
  ti T _ _ = TIZ False
  tisuc _ _ _ _ = TIZ True
  tifin (TIZ tf) = tf
  tiget _ _ _ _ = return Z
  {-# INLINE te #-}
  {-# INLINE ti #-}
  {-# INLINE tisuc #-}
  {-# INLINE tifin #-}
  {-# INLINE tiget #-}

instance ( Index is
         , Index (is:.(Int:.Int))
         , Monad m
         , TEE m ts is
         , NFData (TE ts)
         , VU.Unbox e
         ) => TEE m (ts:.Region e) (is:.(Int:.Int)) where -- (is:.i) where
  type TE (ts:.Region e) = TE ts :. VU.Vector e
  newtype TI (ts:.Region e) (is:.(Int:.Int)) m = TIregion (TI ts is m)
  te (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) = S.map (\z -> z:.VU.unsafeSlice i (j-i) ve) $ te ts is js
  ti (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) = TIregion $ ti ts is js
  tisuc (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) (TIregion as) = TIregion $ tisuc ts is js as
  tifin (TIregion as) = tifin as
  tiget (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) (TIregion as) = tiget ts is js as >>= \z -> return (z:.VU.unsafeSlice i (j-i) ve)
  {-# INLINE te #-}
  {-# INLINE ti #-}
  {-# INLINE tisuc #-}
  {-# INLINE tifin #-}
  {-# INLINE tiget #-}

instance MkElm x i => MkElm (x:.Term ts) i where
  newtype Plm (x:.Term ts) i = Pterm (Elm x i :. Is i :. Is i)
  newtype Elm (x:.Term ts) i = Eterm (Elm x i :. Is i :. TE ts)
  type    Arg (x:.Term ts) = Arg x :. TE ts
  topIdx (Eterm (_ :. k :. _)) = k
  getArg (Eterm (x :. _ :. t)) = getArg x :. t
  {-# INLINE topIdx #-}
  {-# INLINE getArg #-}

instance ( NFData i, NFData (Elm x i), NFData (Is i)
--          , Show ts, Show (Is i), Show i, Show (Elm x i)
          , TEE m ts i
          , NFData (TE ts)
          , NFData (TI ts i m)
          , Index i, Monad m, MkS m x i, MkElm x i, Next ts i) => MkS m (x:.Term ts) i where
  mkS (x:.Term ts) os idx = S.flatten mkT stepT Unknown $ S.flatten mk step Unknown $ mkS x (convT ts os) idx where
    mkT (Pterm (y:.k':.k)) = do
      let stp = ti ts k' k
      stp `deepseq` return (y:.k':.k:.stp)
    stepT (y:.k':.k:.stp)
      | tifin stp = return $ S.Done
      | otherwise = do
          let stp' = tisuc ts k' k stp
          z <- tiget ts k' k stp
          (stp',z) `deepseq` return $ S.Yield (Eterm (y:.k:.z)) (y:.k':.k:.stp')
    mk y = let k = topIdx y in k `deepseq` return (y:.k:.k)
    step (y:.k':.k)
      | leftOfR k idx = let
                          newk = suc ts os idx k' k
                        in newk `deepseq` {- traceShow {- (idx,y,k,ts) -} (k) $ -} return $ S.Yield (Pterm (y:.k':.k)) (y :. k' :. newk)
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkS #-}

instance Next T Z where
  suc T _ Z (IsZ _)  !x = IsZ False
  convT _ (IsTz Z) = IsTz Z
  {-# INLINE suc #-}
  {-# INLINE convT #-}



-- ** NFData instances

instance NFData (TI T Z m) where
  rnf (TIZ b) = rnf b

instance (NFData (TI ts z m)) => NFData (TI (ts:.Region e) (z:.(Int:.Int)) m) where
  rnf (TIregion ts) = rnf ts

instance NFData (Elm ts is) => NFData (Elm (ts :. Term (T :. Region Int)) (is :. (Int :. Int))) where

instance (NFData (Elm (None :. Term (T :. Region Int)) Z)) where

instance NFData (Elm ((None :. Term (T :. Region Int)) :. Term (T :. Region Int)) Z) where

instance NFData (Elm None ((Z :. (Int :. Int)) :. (Int :. Int))) where

instance NFData ((Z :. VU.Vector Int) :. VU.Vector Int) where
