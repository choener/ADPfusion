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
import Control.DeepSeq
import GHC.TypeLits

import Debug.Trace



class MkElm x i where
  data Plm x i :: *
  data Elm x i :: *
  topIdx :: Elm x i -> Is i

class (Index i, Monad m) => MkS m x i where
  mkS :: x -> i -> S.Stream m (Elm x i)



data None = None

instance MkElm None i where
  newtype Plm None i = Pnone (Is i)
  newtype Elm None i = Enone (Is i)
  topIdx (Enone k) = k
  {-# INLINE topIdx #-}

instance (NFData i, NFData (Is i), Index i, Monad m) => MkS m None i where
  mkS None idx = let k = toL idx in (idx,k) `deepseq` S.singleton (Enone k)
  {-
  mkS _ idx = S.unfoldr step True where
    step True  = let k = toL idx in k `deepseq` Just (Enone k, False)
    step False = Nothing
    {-# INLINE step #-}
    -}
  {-# INLINE mkS #-}

data Term ts = Term ts
data T = T

class (Index i) => TermElm x i where
  type TermE x i :: *
  extract :: (Monad m) => x -> Is i -> Is i -> S.Stream m (TermE x i)
  plm2elm :: x -> Is i -> S.Stream m (Plm x i) -> S.Stream m (Elm x i)

instance (Index i) => TermElm T i where
  type TermE T i = Z
  extract _ _ _ = S.singleton Z

instance ( Index (is:.i), TermElm ts is, VU.Unbox e
--         , Is (is:.i) ~ (is:.Int)
         ) => TermElm (ts:.Region e) (is:.i) where
  type TermE (ts:.Region e) (is:.i) = TermE ts is :. VU.Vector e
--  extract (ts:.Region ve) (is:.i) (js:.j) = undefined $ extract ts is js -- S.map (\z -> z:.(VU.unsafeSlice i (j-i) ve)) $ extract ts is js

{-
instance (VU.Unbox e, Index (is:.i), Is (is:.i) ~ (t0:.Int), TermElm t is) => TermElm (t:.Region e) (is:.i) where
  extract (ts:.Region ve) (is:.i) (js:.j) = S.map (\z -> z:.(VU.unsafeSlice i (j-i) ve)) $ extract ts is js
-}

instance MkElm x i => MkElm (x:.Term ts) i where
  newtype Plm (x:.Term ts) i = Pterm (Elm x i :. Is i)
  newtype Elm (x:.Term ts) i = Eterm (Elm x i :. Is i :. TermE ts i)
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

instance ( NFData i, NFData (Elm x i), NFData (Is i)
--          , Show ts, Show (Is i), Show i, Show (Elm x i)
          , Index i, Monad m, MkS m x i, MkElm x i, Next ts i) => MkS m (x:.Term ts) i where
  mkS (x:.Term ts) idx = S.map undefined $ S.flatten mk step Unknown $ mkS x idx where
    mk y = let k = topIdx y in k `deepseq` return (y:.k:.k)
    step (y:.k':.k)
      | leftOfR k idx = let
                          newk = suc ts idx k' k
                        in newk `deepseq` {- traceShow {- (idx,y,k,ts) -} (k) $ -} return $ S.Yield (Pterm (y:.k)) (y :. k' :. newk)
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
--  x <- S.length $ mkS None (Z:.(i:.j))
  x <- S.length $ mkS (None :. Term (T:.Region xs)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region ys)) (Z:.(i,j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (Z:.(i,j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (Z:.(i,j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs:.Region xs) :. Term (T:.Region xs:.Region xs)) (Z:.(i,j):.(i,j))
  return $ x
{-# NOINLINE testInner #-}

-- *

class (Index i) => Next x i where
  suc :: x -> i -> Is i -> Is i -> Is i
--  fin :: x -> i -> Is i -> Bool

instance Next T Z where
  suc T Z True  !x = False
  suc T Z False !x = False
--  fin T Z ft = not ft
  {-# INLINE suc #-}
--  {-# INLINE fin #-}

instance Next x y => Next (x:.Region Int) (y:.(Int:.Int)) where
  suc (x:.r) (ix:.(i:.j)) (ks':.k') (z:.k)
--    | fin x ix z = z:.k+1
    | k<j = z :. k+1
    | otherwise = suc x ix ks' z :. k'
--  fin (x:.r) (ix:.(i,j)) (z:.k) = {- k>=j && -} fin x ix z
  {-# INLINE suc #-}
--  {-# INLINE fin #-}

class Index i where
  type Is i :: *
  toL :: i -> Is i
  toR :: i -> Is i
  from :: Is i -> Is i -> i
  leftOfR :: Is i -> i -> Bool

instance Index z => Index (z:.Int) where
  type Is (z:.Int) = Is z:.Int
  toL (z:.i) = toL z :. i
  toR (z:.i) = toR z :. i
  from (z:.i) (z':._) = from z z' :. i
  leftOfR (z:.i) (z':.j) = leftOfR z z' -- || i<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index z => Index (z:.(Int:.Int)) where
  type Is (z:.(Int:.Int)) = Is z:.Int
  toL (z:.(i:.j)) = toL z:.i
  toR (z:.(i:.j)) = toR z:.j
  from (z:.i) (z':.j) = from z z' :.(i:.j)
  leftOfR (z:.k) (z':.(i:.j)) = leftOfR z z' -- || k<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index Z where
  type Is Z = Bool
  toL Z = True
  toR Z = True
  from _ _ = Z
  leftOfR ft Z = ft
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
