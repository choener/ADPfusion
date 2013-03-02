{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{- OPTIONS_GHC -funbox-strict-fields #-}

module ADP.Fusion.Classes where

import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Primitive.Types (Prim(..))
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import Control.DeepSeq
import GHC.TypeLits

import Debug.Trace



class MkElm x i where
  data Plm x i :: *
  data Elm x i :: *
  topIdx :: Elm x i -> Is i

class (Index i, Monad m) => MkS m x i where
  mkS :: x -> IsT i -> i -> S.Stream m (Elm x i)



data None = None

instance MkElm None i where
  newtype Plm None i = Pnone (Is i)
  newtype Elm None i = Enone (Is i)
  topIdx (Enone k) = k
  {-# INLINE topIdx #-}

instance (NFData i, NFData (Is i), Index i, Monad m) => MkS m None i where
  mkS None _ idx = let k = toL idx in (idx,k) `deepseq` S.singleton (Enone k)
  {-
  mkS _ idx = S.unfoldr step True where
    step True  = let k = toL idx in k `deepseq` Just (Enone k, False)
    step False = Nothing
    {-# INLINE step #-}
    -}
  {-# INLINE mkS #-}

data Term ts = Term ts
data T = T

{-
class TermElm x where
  type TermE x :: *
  type TermI x :: *
  extract :: (Monad m) => x -> TermI x -> TermI x -> S.Stream m (TermE x)

instance TermElm T where
  type TermE T = Z
  type TermI T = Z
  extract _ _ _ = S.singleton Z

instance (TermElm ts, VU.Unbox e) => TermElm (ts:.Region e) where
  type TermE (ts:.Region e) = TermE ts :. VU.Vector e
  type TermI (ts:.Region e) = TermI ts :. Int
  extract (ts:.Region ve) (is:.i) (js:.j) = S.map (\z -> z :. VU.unsafeSlice i (j-i) ve) $ extract ts is js
-}

class (Monad m) => TEE m x i where
  type TE x :: *
  data TI x i m :: *
  te :: x -> Is i -> Is i -> S.Stream m (TE x)
  ti :: x -> Is i -> Is i -> (TI x i m)
  tisuc :: x -> Is i -> Is i -> TI x i m -> (TI x i m)
  tifin :: TI x i m -> Bool
  tiget :: x -> Is i -> Is i -> TI x i m -> m (TE x)

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
  topIdx (Eterm (_ :. k :. _)) = k
  {-# INLINE topIdx #-}

deriving instance Show (Elm None (Z:.(Int:.Int)))
--deriving instance Show (Elm (None :. Term (T :. Region Int)) (Z :. (Int:.Int)))
deriving instance Show (Region Int)
deriving instance Show T
deriving instance Show (Elm None ((Z :. (Int:.Int)) :. (Int:.Int)))
--deriving instance Show (Elm (None :. Term ((T :. Region Int) :. Region Int)) ((Z :. (Int:.Int)) :. (Int:.Int)))

instance (NFData a, NFData b) => NFData (a:.b) where
  rnf (a:.b) = rnf a `seq` rnf b `seq` ()

instance NFData Z where
  rnf Z = ()

instance NFData (Is k) => NFData (Elm None k) where
  rnf (Enone k) = rnf k

instance NFData None

instance (NFData (Is is), NFData x, NFData (Elm x is), NFData (TE ts)) => NFData (Elm (x:.Term ts) is) where
  rnf (Eterm (x:.is:.ts)) = rnf x `seq` rnf is `seq` rnf ts

instance (NFData a, NFData s) => NFData (S.Step a s) where
  rnf S.Done = ()
  rnf (S.Skip s) = rnf s
  rnf (S.Yield a s) = rnf a `seq` rnf s

instance NFData (TI T Z m) where
  rnf (TIZ b) = rnf b

instance (NFData (TI ts z m)) => NFData (TI (ts:.Region e) (z:.(Int:.Int)) m) where
  rnf (TIregion ts) = rnf ts

instance NFData (Term (T:. Region Int)) where

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

data Region e = Region !(VU.Vector e)

test :: Int -> IO Int
test k =
  let
    xs = VU.fromList [0 .. 2 :: Int]
    ys = VU.reverse xs
    i = 0 :: Int
    j = k :: Int
  in do
    (xs,ys,i,j) `deepseq` testInner k xs ys i j
{-# NOINLINE test #-}

testInner :: Int -> VU.Vector Int -> VU.Vector Int -> Int -> Int -> IO Int
testInner !k !xs !ys !i !j = do
--  x <- return 1
--  x <- S.length $ mkS None (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region ys)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (Z:.(i,j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs:.Region xs) :. Term (T:.Region xs:.Region xs)) (Z:.(i:.j):.(i:.j))
  return $ x
{-# NOINLINE testInner #-}

-- *

class (Index i) => Next x i where
  suc :: x -> IsT i -> i -> Is i -> Is i -> Is i
  convT :: x -> IsT i -> IsT i

instance Next T Z where
  suc T _ Z (IsZ _)  !x = IsZ False
  convT _ (IsTz Z) = IsTz Z
  {-# INLINE suc #-}
  {-# INLINE convT #-}

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

data OIR
  = Outer
  | Inner
  | Restricted
  deriving (Eq)

class Index i where
  data Is i :: *
  data IsT i :: *
  toL :: i -> Is i
  toR :: i -> Is i
  from :: Is i -> Is i -> i
  leftOfR :: Is i -> i -> Bool

instance Index z => Index (z:.Int) where
  newtype Is (z:.Int) = IsInt (Is z:.Int)
  newtype IsT (z:.Int) = IsTint (IsT z :. OIR)
  toL (z:.i) = IsInt $ toL z :. i
  toR (z:.i) = IsInt $ toR z :. i
  from (IsInt (z:.i)) (IsInt (z':._)) = from z z' :. i
  leftOfR (IsInt (z:.i)) (z':.j) = leftOfR z z' -- || i<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index z => Index (z:.(Int:.Int)) where
  newtype Is (z:.(Int:.Int)) = IsIntInt (Is z:.Int)
  newtype IsT (z:.(Int:.Int)) = IsTii (IsT z :. OIR)
  toL (z:.(i:.j)) = IsIntInt $ toL z:.i
  toR (z:.(i:.j)) = IsIntInt $ toR z:.j
  from (IsIntInt (z:.i)) (IsIntInt (z':.j)) = from z z' :.(i:.j)
  leftOfR (IsIntInt (z:.k)) (z':.(i:.j)) = leftOfR z z' -- || k<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance (NFData (Is z)) => NFData (Is (z:.(Int:.Int))) where
  rnf (IsIntInt (z:.k)) = k `seq` rnf z

deriving instance (Show (Is z)) => Show (Is (z:.(Int:.Int)))

instance Index Z where
  newtype Is Z = IsZ Bool
  newtype IsT Z = IsTz Z
  toL Z = IsZ True
  toR Z = IsZ True
  from _ _ = Z
  leftOfR (IsZ ft) Z = ft
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance NFData (Is Z) where
  rnf (IsZ b) = rnf b

deriving instance Show (Is Z)

