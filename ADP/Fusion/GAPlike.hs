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
type instance TopW LR = W LR

type family   TopIdx x :: *
type instance TopIdx Z = Z:.Int
type instance TopIdx (x:.y) = TopIdx x :. TopIdx y
type instance TopIdx Chr = Int
type instance TopIdx Dhr = Int
type instance TopIdx (VUM.MVector s elm) = Int
type instance TopIdx LR = Int

type family   TopArg x :: *
type instance TopArg Z = Z
type instance TopArg (x:.y) = TopArg x :. TopArg y
type instance TopArg Chr = Char
type instance TopArg Dhr = Char
type instance TopArg (VUM.MVector s elm) = elm
type instance TopArg LR = Int

data W t = W

type StepType m x y
  =  (TopW x:.TopW y, TopIdx x:.TopIdx y, TopArg x)
  -> m (S.Step (TopW x:.TopW y, TopIdx x:.TopIdx y, TopArg x) (TopW x:.TopW y, TopIdx x:.TopIdx y, TopArg x:.TopArg y))

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

instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.Dhr) where
  type SC (x:.Dhr) = ()
  mkStream (x:.Dhr (!ds)) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zw,zi:.k,za) = return $ (zw:.W, zi:.k:.k, za)
    step :: StepType m x Dhr
    step (zw,(zi:.k),za)
      | k<=j      = do  let c = ds ! (Z:.k)
                        return $ S.Yield (zw,zi:.k,za:.c) (zw,zi:.j+1,za)
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

instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.LR) where
  type SC (x:.LR) = (Get x)
  mkStream (x:.LR limit lr) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zw,zi:.k,za) = return $ (zw:.W, zi:.k:.k, za)
    step :: StepType m x LR
    step (zw,zi:.k,za)
      | k<=j && dd <= limit = do  let c = VU.unsafeIndex lr k
                                  return $ S.Yield (zw,zi:.k,za:.c) (zw,zi:.j+1,za)
      | otherwise = return $ S.Done
      where dd = down (x,zi)
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
  getI :: (x, TopIdx x) -> Int
  down :: (x, TopIdx x) -> Int

instance Get Z where
  getI (_,zi:.k) = k
  down _          = 0
  {-# INLINE getI #-}
  {-# INLINE down #-}

instance Get x => Get (x:.LR) where
  getI (_,_:.k) = k
  down (x:._,zi:.k) = down (x,zi) + (k - getI (x,zi))
  {-# INLINE getI #-}
  {-# INLINE down #-}

instance Get x => Get (x:.Dhr) where
  getI (_,_:.k) = k
  down (x:._,zi:._) = down (x,zi)
  {-# INLINE getI #-}
  {-# INLINE down #-}

testZ i j = SPure.length $ mkStream (Z:.ccc) (Z:.i:.j)
{-# NOINLINE testZ #-}

testST :: Dhr -> Int -> Int -> Int
testST inp i j = runST $ embedST inp i j
{-# NOINLINE testST #-}

embedST :: Dhr -> Int -> Int -> ST s Int
embedST inp i j = do
  vm :: VUM.MVector s Int <- VUM.replicate 10 0
  vn :: VUM.MVector s Int <- VUM.replicate 10 0
  (fici <<< lr ~~ inp ~~ lr ... (S.foldl' (+) 0)) (Z:.i:.j)
{-# NOINLINE embedST #-}

infix 8 <<<
(<<<) f t ij = S.map (\(_,_,za) -> apply f za) $ stream (build t) ij
{-# INLINE (<<<) #-}

infix 7 ...
(...) s h ij = h $ s ij
{-# INLINE (...) #-}

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

fici :: Int -> Char -> Int -> Int
fici i c j = i + ord c + j

cv :: Char -> Int -> Int
cv c i = case c of
  'A' -> 1+i
  _   -> 2+i
{-# INLINE cv #-}


data Chr = Chr !(VU.Vector Char)
ccc = dvu `seq` Chr dvu
{-# NOINLINE ccc #-}

instance Show Chr where
  show _ = "Chr"

data Dhr = Dhr !(Arr0 DIM1 Char)
ddd = Dhr $ fromAssocs (Z:.0) (Z:.10) 'a' []
{-# NOINLINE ddd #-}

instance Show Dhr where
  show _ = "Dhr"

data LR = LR Int !(VU.Vector Int)
lr = LR 15 (VU.fromList [1 .. 100])
{-# NOINLINE lr #-}

instance Show LR where
  show _ = "LR"

infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}

class Build x where
  type Bld x :: *
  build :: x -> Bld x

instance Build x => Build (x,y) where
  type Bld (x,y) = Bld x :. y
  build (a,b) = build a :. b
  {-# INLINE build #-}

instance Build Chr where
  type Bld Chr = Z:.Chr
  build a = Z:.a
  {-# INLINE build #-}

instance Build (VUM.MVector s elm) where
  type Bld (VUM.MVector s elm) = Z:.VUM.MVector s elm
  build a = Z:.a
  {-# INLINE build #-}

instance Build LR where
  type Bld LR = Z:.LR
  build a = Z:.a

dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}
