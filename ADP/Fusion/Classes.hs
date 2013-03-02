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
  data TEstepper x i :: *
  te :: x -> Is i -> Is i -> S.Stream m (TE x)
  te' :: x -> Is i -> Is i -> m (S.Step (TEstepper x i) (TE x))
  go' :: x -> Is i -> Is i -> TEstepper x i -> m (S.Step (TEstepper x i) (TE x))

instance (Monad m) => TEE m T Z where
  type TE T = Z
  newtype TEstepper T Z = TEstepperZ Z
  te T _ _ = S.singleton Z
  te' T _ _ = return $ S.Yield Z (TEstepperZ Z)
  go' _ _ _ _ = return $ S.Done
  {-# INLINE te #-}
  {-# INLINE te' #-}
  {-# INLINE go' #-}

instance NFData (TEstepper T Z) where
  rnf (TEstepperZ z) = rnf z

instance (NFData (TEstepper ts is)) => NFData (TEstepper (ts:.Region e) (is:.(Int:.Int))) where
  rnf (TEstepperRegion (stp :. z)) = rnf stp `seq` rnf z

instance ( Index is
         , Index (is:.(Int:.Int))
         , Monad m
         , TEE m ts is
         , NFData (TE ts)
         , NFData (TEstepper ts is)
         , VU.Unbox e
         ) => TEE m (ts:.Region e) (is:.(Int:.Int)) where -- (is:.i) where
  type TE (ts:.Region e) = TE ts :. VU.Vector e
  newtype TEstepper (ts:.Region e) (is:.(Int:.Int)) = TEstepperRegion (TEstepper ts is :. Z)
  te (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) = S.map (\z -> z:.VU.unsafeSlice i (j-i) ve) $ te ts is js
  te' (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) = do
    stp <- te' ts is js
    case stp of
      S.Done      -> return $ S.Done
      S.Yield a s -> (a,s) `deepseq` return $ S.Yield (a:.VU.unsafeSlice i (j-i) ve) (TEstepperRegion (s:.Z))
  go' (ts:.Region ve) (IsIntInt (is:.i)) (IsIntInt (js:.j)) (TEstepperRegion (ss :. s)) = do
    stp <- go' ts is js ss
    case stp of
      S.Done -> return $ S.Done
      S.Yield a s -> (a,s) `deepseq` return $ S.Yield (a:.VU.unsafeSlice i (j-i) ve) (TEstepperRegion (s:.Z))
  {-# INLINE te #-}
  {-# INLINE te' #-}
  {-# INLINE go' #-}

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

instance ( NFData i, NFData (Elm x i), NFData (Is i)
--          , Show ts, Show (Is i), Show i, Show (Elm x i)
          , TEE m ts i
          , NFData (TE ts)
          , NFData (TEstepper ts i)
          , Index i, Monad m, MkS m x i, MkElm x i, Next ts i) => MkS m (x:.Term ts) i where
  mkS (x:.Term ts) idx = S.flatten mkT stepT Unknown $ S.flatten mk step Unknown $ mkS x idx where
    mkT (Pterm (y:.k':.k)) = do
               stp <- te' ts k' k
               stp `deepseq` return (y:.k':.k:.stp)
    stepT (y:.k':.k:.stp) = case stp of
      S.Done      -> return $ S.Done
      S.Yield a s -> do stp' <- go' ts k' k s
                        stp' `seq` return $ S.Yield (Eterm (y:.k:.a)) (y:.k':.k:.stp')
    mk y = let k = topIdx y in k `deepseq` return (y:.k:.k)
    step (y:.k':.k)
      | leftOfR k idx = let
                          newk = suc ts idx k' k
                        in newk `deepseq` {- traceShow {- (idx,y,k,ts) -} (k) $ -} return $ S.Yield (Pterm (y:.k':.k)) (y :. k' :. newk)
      | otherwise = return $ S.Done
    {-# INLINE mkT #-}
    {-# INLINE stepT #-}
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
--  x <- S.length $ mkS (None :. Term (T:.Region xs)) (Z:.(i:.j))
  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region ys)) (Z:.(i:.j))
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
  suc T Z (IsZ True)  !x = IsZ False
  suc T Z (IsZ False) !x = IsZ False
--  fin T Z ft = not ft
  {-# INLINE suc #-}
--  {-# INLINE fin #-}

instance Next x y => Next (x:.Region Int) (y:.(Int:.Int)) where
  suc (x:.r) (ix:.(i:.j)) (IsIntInt (ks':.k')) (IsIntInt (z:.k))
--    | fin x ix z = z:.k+1
    | k<j = IsIntInt $ z :. k+1
    | otherwise = IsIntInt $ suc x ix ks' z :. k'
--  fin (x:.r) (ix:.(i,j)) (z:.k) = {- k>=j && -} fin x ix z
  {-# INLINE suc #-}
--  {-# INLINE fin #-}

class Index i where
  data Is i :: *
  toL :: i -> Is i
  toR :: i -> Is i
  from :: Is i -> Is i -> i
  leftOfR :: Is i -> i -> Bool

instance Index z => Index (z:.Int) where
  newtype Is (z:.Int) = IsInt (Is z:.Int)
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
