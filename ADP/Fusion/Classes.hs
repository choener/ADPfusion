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

module ADP.Fusion.Classes where

import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Primitive.Types (Prim(..))
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq
import GHC.TypeLits

import Debug.Trace



class MkElm x i where
  data Elm x i :: *
  topIdx :: Elm x i -> Is i

class (Index i, Monad m) => MkS m x i where
  mkS :: x -> i -> S.Stream m (Elm x i)



data None = None

instance MkElm None i where
  newtype Elm None i = Enone (Is i)
  topIdx (Enone !k) = k
  {-# INLINE topIdx #-}

instance (Index i, NFData i, NFData (Is i), Monad m) => MkS m None i where
  mkS _ idx = idx `deepseq` S.unfoldr step True where
    step True  = let k = toL idx in k `deepseq` Just (Enone k, False)
    step False = Nothing
  {-# INLINE mkS #-}


data Term ts = Term ts

instance MkElm x i => MkElm (x:.Term ts) i where
  newtype Elm (x:.Term ts) i = Eterm (Elm x i, Is i, ts)
  topIdx (Eterm (_,!k,_)) = k
  {-# INLINE topIdx #-}

instance NFData (Z:.Int) where
  rnf (Z:.i) = rnf i
  {-# INLINE rnf #-}

instance NFData (Z:.Int:.Int) where
  rnf (Z:.i:.j) = i `seq` rnf j
  {-# INLINE rnf #-}

instance NFData (Z:.(Int,Int)) where
  rnf (Z:.(i,j)) = i `seq` rnf j
  {-# INLINE rnf #-}

instance NFData (Z:.(Int,Int):.(Int,Int)) where
  rnf (Z:.(i,j):.(k,l)) = i `seq` j `seq` k `seq` rnf l
  {-# INLINE rnf #-}

instance (NFData (Is i), NFData i, Index i, Monad m, MkS m x i, MkElm x i, Next ts i) => MkS m (x:.Term ts) i where
--  mkS (x:.Term ts) idx = S.map (\y -> Eterm y (topIdx y) ts) $ mkS x idx
  mkS (x:.Term ts) idx = idx `deepseq` S.flatten mk step Unknown $ mkS x idx where
    mk :: Elm x i -> m (Elm x i, Is i)
    mk y = let k = topIdx y in k `deepseq` return (y, k)
    step :: (Elm x i, Is i) -> m (S.Step (Elm x i, Is i) (Elm (x:.Term ts) i))
    step (y,k)
      | leftOfR k idx = return $ S.Yield (Eterm (y,k,ts)) (y,suc ts idx k)
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkS #-}



data Region e = Region !(VU.Vector e)

test :: Int -> IO Int
test k =
  let
    xs = VU.fromList [1 .. 10 :: Int]
    i = 0 :: Int
    j = 10 :: Int
  in do
    (xs,i,j) `deepseq` testInner k xs i j
{-# NOINLINE test #-}

testInner :: Int -> VU.Vector Int -> Int -> Int -> IO Int
testInner !k !xs !i !j = do
  x <- S.length $ S.take k $ mkS (None :. Term (Z:.Region xs)) (Z:.(i,j))
--  y <- S.length $ S.take k $ mkS (None :. Term (Z:.Region xs:.Region xs) :. Term (Z:.Region xs:.Region xs)) (Z:.(i,j):.(i,j))
--  y <- S.length $ S.take k $ mkS (None :. Term (Z:.Region xs) :. Term (Z:.Region xs)) (Z:.(i,j))
  y <- return 1
  return $ x+y
{-# NOINLINE testInner #-}

-- *

class (Index i) => Next x i where
  suc :: x -> i -> Is i -> Is i

instance Next Z Z where
  suc Z Z Z = Z

instance Next x y => Next (x:.Region Int) (y:.(Int,Int)) where
  suc (x:.r) (ix:.(i,j)) (z:.k) = suc x ix z :. k+1

{-
instance Next (Z:.Region Int) (Z:.(Int,Int)) where
  suc !a !b !(Z:.k) = Z:.k+1
  {-# INLINE suc #-}
-}

class Index x where
  type Is x :: *
  toL :: x -> Is x
  toR :: x -> Is x
  from :: Is x -> Is x -> x
  leftOfR :: Is x -> x -> Bool


instance Index z => Index (z:.Int) where
  type Is (z:.Int) = Is z:.Int
  toL (z:.i) = toL z :. i
  toR (z:.i) = toR z :. i
  from (z:.i) (z':._) = from z z' :. i
  leftOfR (z:.i) (z':.j) = leftOfR z z' || i<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index z => Index (z:.(Int,Int)) where
  type Is (z:.(Int,Int)) = Is z:.Int
  toL (z:.(i,j)) = toL z:.i
  toR (z:.(i,j)) = toR z:.j
  from (z:.i) (z':.j) = from z z' :.(i,j)
  leftOfR (z:.k) (z':.(i,j)) = leftOfR z z' || k<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index Z where
  type Is Z = Z
  toL _ = Z
  toR _ = Z
  from _ _ = Z
  leftOfR _ _ = True
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}


































{-

-- *

type family Depth d :: Nat
type instance Depth Z = 0
type instance Depth (t:.h) = Depth t + 1

-- *

data IdxType
  = IdxO

-- *

class SElement x n where
  data SElm x n :: *
  getIs :: SElm x n -> Is n

class (MkSC x) => MkS m x where
  type MkSC x :: Constraint
  type MkSC x = ()
  mkStream :: (MkSC x, Index sh, Depth idxt ~ Depth sh) => x -> (idxt,sh) -> S.Stream m (SElm x sh)

-- *

data None = None

instance SElement None n where
  data SElm None n = SeNone (Is n)
  getIs (SeNone k) = k

instance (Monad m) => MkS m None where
  mkStream None (_,idx) = S.singleton $ SeNone (toL idx)

-- *

data Region e = Region (VU.Vector e)

type family Elem x :: *
type instance Elem Z = Z
type instance Elem (x:.Region e) = Elem x :. e

-- *



-- *

data Term xs = Term xs

class GetElem x where
  getElem :: x -> x -> Elem x

instance (SElement x n, Depth ts ~ Depth n) => SElement (x:.Term ts) n where
  data SElm (x:.Term ts) n = SeTerm (SElm x n) (Is n) (Elem ts)
  getIs (SeTerm _ k _) = k

instance (Monad m, MkS m x, SElement (x:.Term ts) (Depth ts)) => MkS m (x:.Term ts) where
  mkStream (x:.Term ts) (ixt,idx) = S.flatten mk step Unknown $ mkStream x (ixt,idx) where
    mk x' = return (x', getIs x')
    step (x', k)
--      | valid (getIs x') (toR idx) k = return $ S.Yield (SeTerm x' k (getElem ts k)) (x', nextIdx k)
      | otherwise = return $ S.Done

-- *

test = do
  let v = VU.fromList [1 .. 10 :: Int]
  xs <- S.toList $ mkStream (None :. Term (Z:.Region v)) (Z:.IdxO, Z:.(1::Int,10::Int))
  print $ length xs
{-# NOINLINE test #-}


-}
