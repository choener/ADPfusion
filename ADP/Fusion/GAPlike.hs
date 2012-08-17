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

type family STtop x :: *
type instance STtop Z   = (W Z  , Int)
type instance STtop Chr = (W Chr, Int)
type instance STtop (VUM.MVector s elm) = (W (VUM.MVector s elm), Int)

type family Stack x :: *
type instance Stack Z = Z:.STtop Z
type instance Stack (x:.y) = Stack x :. STtop y

data W t = W

class Monad m => MkStream m x where
  type SC x :: Constraint
  type SC x = ()
  mkStream :: (SC x) => x -> DIM2 -> S.Stream m (Stack x)

instance (Monad m) => MkStream m Z where
  mkStream Z (Z:.i:.j) = S.unfoldr step i where
    step i
      | i<=j      = Just (Z:.(W,i), (j+1))
      | otherwise = Nothing
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m x, SC x) => MkStream m (x:.Chr) where
  type SC (x:.Chr) = (Get (Stack x))
  mkStream (x:.Chr cs) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk z = return $ z:.(W, get z)
    step zj@(z:.(w, k))
      | k<=j      = return $ S.Yield zj (z:.(w,(j+1)))
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m x, SC x) => MkStream m (x:.VUM.MVector s elm) where
  type SC (x:.VUM.MVector s elm) = (Get (Stack x))
  mkStream (x:.mvec) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk z = return $ z:.(W, get z)
    step zj@(z:.(w, k))
      | k<=j      = return $ S.Yield zj (z:.(w,(j+1)))
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

class Get x where
  get :: x -> Int

instance Get Z where
  get _ = undefined
  {-# INLINE get #-}

instance  Get (x:.(W y, Int)) where
  get (_:.(_,i)) = i
  {-# INLINE get #-}

testZ i j = SPure.length $ mkStream (Z:.ccc) (Z:.i:.j)
{-# NOINLINE testZ #-}

testST :: Int -> Int -> Int
testST i j = runST $ embedST i j
{-# NOINLINE testST #-}

embedST :: Int -> Int -> ST s Int
embedST i j = do
  vm :: VUM.MVector s Int <- VUM.replicate 10 0
  v <- S.length $ mkStream (Z:.ccc:.vm) (Z:.i:.j)
  return v
{-# INLINE embedST #-}



data Chr = Chr (VU.Vector Char)
ccc = Chr dvu



infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}


dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}
