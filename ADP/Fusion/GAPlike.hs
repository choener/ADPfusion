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
import ADP.Fusion.Monadic.Internal (Apply(..))
import Data.Char

type family ST x :: *
type instance ST Z   = (W Z  , Int)
type instance ST Chr = (W Chr, Int)

type family Stack x :: *
type instance Stack Z = Z:.ST Z
type instance Stack (x:.y) = Stack x :. ST y

data W t = W

class Monad m => MkStream m x where
  type SC x :: Constraint
  type SC x = ()
  mkStream :: (SC x) => x -> DIM2 -> S.Stream m (Stack x)

instance (Monad m) => MkStream m Z where
  mkStream Z (Z:.i:.j) = i `seq` j `seq` S.unfoldr step i where
    step i
      | i<=j      = Just (Z:.(W,i), (j+1))
      | otherwise = Nothing
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m x, SC x) => MkStream m (x:.Chr) where
  type SC (x:.Chr) = (Get (Stack x))
  mkStream (x:.Chr cs) (Z:.i:.j) = i `seq` j `seq` cs `seq` x `seq` S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk z = z `seq` return $ z:.(W, get z)
    step zj@(z:.(w, k))
      | k<=j      = zj `seq` z `seq` w `seq` k `seq` return $ S.Yield zj (z:.(w,(j+1)))
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


data Chr = Chr (VU.Vector Char)
ccc = Chr dvu



infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}


dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}
