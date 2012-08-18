{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{- LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module ADP.Fusion.GAPlike where

import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Fusion.Stream as SPure
import Data.Vector.Fusion.Stream.Size
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import Text.Printf
import GHC.Prim (Constraint(..))
import Debug.Trace
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import ADP.Fusion.Monadic.Internal (Apply(..))
import Data.Char
import Control.Monad.ST
import Control.Monad.Primitive
import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.Zero
import Data.Primitive

type family   TopW x :: *
type instance TopW Z   = Z
type instance TopW (x:.y) = TopW x :. TopW y
type instance TopW Chr = W Chr
type instance TopW Dhr = W Dhr
type instance TopW (VUM.MVector s elm) = W (VUM.MVector s elm)

type family   TopIdx x :: *
type instance TopIdx Z = Z:.Int
type instance TopIdx (x:.y) = TopIdx x :. TopIdx y
type instance TopIdx Chr = Int
type instance TopIdx Dhr = Int
type instance TopIdx (VUM.MVector s elm) = Int

type family   TopArg x :: *
type instance TopArg Z = Z
type instance TopArg (x:.y) = TopArg x :. TopArg y
type instance TopArg Chr = Char
type instance TopArg Dhr = Char
type instance TopArg (VUM.MVector s elm) = elm

data W t = W

class (Monad m, DS x) => MkStream m x where
  type SC x :: Constraint
  type SC x = ()
  mkStream :: (SC x) => x -> DIM2 -> S.Stream m (TopW x, TopIdx x, TopArg x)
  stream   :: (SC x) => x -> DIM2 -> S.Stream m (TopW x, TopIdx x, TopArg x)
  stream x ij = ds x `seq` ij `seq` mkStream x ij
  {-# INLINE stream #-}

instance (Monad m) => MkStream m Z where
  mkStream Z (Z:.i:.j) = S.unfoldr step i where
    step i
      | i<=j      = Just ((Z, Z:.i, Z), (j+1))
      | otherwise = Nothing
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.Chr) where
  type SC (x:.Chr) = ()
  mkStream (x:.Chr cs) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zw,zi,za) = let (_:.k) = zi in return (zw:.W, zi:.k, za)
    step (zw,zi,za)
      | k<=j      = c `seq` return $ S.Yield (zw,zi,za:.c) (zw,zi':.j+1,za)
      | otherwise = return $ S.Done
      where (zi':.k) = zi
            c        = VU.unsafeIndex cs k
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

instance (Monad m, {- PrimMonad m, Functor m, PrimState m ~ s, -} MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.Dhr) where
  type SC (x:.Dhr) = ()
  mkStream (x:.Dhr (!ds)) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zw,zi:.k,za) = return $ (zw:.W, zi:.k:.k, za)
    step :: (TopW x:.W Dhr, TopIdx x:.Int, TopArg x) -> m (S.Step (TopW x:.W Dhr, TopIdx x:.Int, TopArg x) (TopW x:.W Dhr, TopIdx x:.Int, TopArg x:.Char))
    step (zw,(zi:.k),za)
      | k<=j      = do  let c = ds ! (Z:.k)
                        return $ S.Yield (zw,zi:.k,za:.c) (zw,zi:.j+1,za)
    {-
      | k<=j = do let (Arr0 sh xxx) = ds
                  mds <- (MArr0 sh) `fmap` unsafeThawByteArray xxx
                  c <- readM mds (Z:.k)
                  return $ S.Yield (zw,zi:.k,za:.c) (zw,zi:.j+1,za)
                        -}
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

instance (Monad m, PrimMonad m, VUM.Unbox elm, PrimState m ~ s, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.VUM.MVector s elm) where
  type SC (x:.VUM.MVector s elm) = ()
  mkStream (x:.mvec) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zw,zi:.k,za) = return $ (zw:.W, zi:.k:.k, za)
    step (zw,zi:.k,za)
      | k<=j      = do  c <- VUM.unsafeRead mvec k
                        return $ S.Yield (zw,zi:.k,za:.c) (zw,zi:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

class DS x where
  ds :: x -> y -> y

instance DS Z where
  ds Z a = a
  {-# INLINE ds #-}

instance DS x => DS (x:.y) where
  ds (x:.y) a = ds x (y `seq` a)
  {-# INLINE ds #-}

class Get x where
  get :: x -> Int

{-
instance Get Z where
  get _ = undefined
  {-# INLINE get #-}

instance  Get (x:.(W y, Int)) where
  get (_:.(_,i)) = i
  {-# INLINE get #-}
-}

testZ i j = SPure.length $ mkStream (Z:.ccc) (Z:.i:.j)
{-# NOINLINE testZ #-}

testST :: Dhr -> Int -> Int -> Int
testST inp i j = runST $ embedST inp i j
{-# NOINLINE testST #-}

embedST :: Dhr -> Int -> Int -> ST s Int
embedST inp i j = do
  vm :: VUM.MVector s Int <- VUM.replicate 10 0
  vn :: VUM.MVector s Int <- VUM.replicate 10 0
  S.foldl' (+) 0 $ S.map (\(zw,zi,za) -> apply fic za) $ stream (Z:.vm:.inp) (Z:.i:.j)
{-# NOINLINE embedST #-}

gnignu f (Z:.a:.b) = a `seq` b `seq` f a b
{-# INLINE gnignu #-}

fii :: Int -> Int -> Int
fii i j = i+j
{-# INLINE fii #-}

fiic :: Int -> Int -> Char -> Int
fiic i j c = i `seq` j `seq` c `seq` ord c + i+j
{-# INLINE fiic #-}

fic :: Int -> Char -> Int
fic i c = i `seq` c `seq` ord c + i
{-# INLINE fic #-}

cv :: Char -> Int -> Int
cv c i = case c of
  'A' -> 1+i
  _   -> 2+i
{-# INLINE cv #-}


data Chr = Chr !(VU.Vector Char)
ccc = dvu `seq` Chr dvu
{-# NOINLINE ccc #-}

data Dhr = Dhr !(Arr0 DIM1 Char)
ddd = Dhr $ fromAssocs (Z:.0) (Z:.10) 'a' []
{-# NOINLINE ddd #-}


infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}


dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}
