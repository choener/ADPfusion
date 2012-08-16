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


class Expr sem where
  type Pre sem a :: Constraint
  constant :: Pre sem a => a -> sem a
  add :: Pre sem a => sem a -> sem a -> sem a

data E a = E {eval :: a}

instance Expr E where
  type Pre E a = Num a
  constant c = E c
  add e1 e2 = E $ (eval e1) + (eval e2)

class Arg x where
  type C x s :: Constraint
  type C x s = (Get s) -- s.th. like s ~ (_:.Int)
  mk   :: (C x s) => x ->               s -> (s:.Int)
  grd  :: (C x s) => x -> Int -> (s:.Int) -> Bool
  next :: (C x s) => x -> Int -> (s:.Int) -> (s:.Int)

class Get x where
  get :: x -> Int
  put :: x -> Int -> x

instance Get Z where
  get _ = undefined
  put _ _ = undefined

instance Get (z:.Int) where
  get (z:.x) = x
  put (z:._) x = (z:.x)

data Chr = Chr (VU.Vector Char)
c = Chr dvu

instance Arg Chr where
  type C Chr s = (Get s) -- s.th. like s ~ (_:.Int)
  mk   _   z = (z:.get z)
  grd  _ j z = get z <= j
  next _ j z = put z (get z + 1)

data Dhr = Dhr (VU.Vector Char)
d = Dhr dvu

class Get2 x where
  get2 :: x -> (Int,Int)
  put2 :: x -> (Int,Int) -> x

instance Get2 Z where
  get2 _ = undefined
  put2 _ _ = undefined

instance Get2 (z:.Int:.Int) where
  get2 (z:.x:.y) = (x,y)
  put2 (z:._:._) (x,y) = (z:.x:.y)

instance Arg Dhr where
  type C Dhr s = (Get s, Get2 s)
  mk   _   z = (z:.get z)
  grd  _ j z = get z <= j -- && get2 z == (1,3)
  next _ j z = put z (get z + 1)

type family Stack x :: *
type instance Stack Z = Z:.Int
type instance Stack (x:.y) = Stack x :. Int

class (Monad m) => MkStack m x where
  mkStack :: x -> DIM2 -> S.Stream m (Stack x)

instance (Monad m) => MkStack m Z where
  mkStack Z (Z:.i:.j) = S.singleton (Z:.i)

instance (Monad m, MkStack m x, Arg y, Stack x ~ (t0:.Int)) => MkStack m (x:.y) where
  mkStack (x:.y) (Z:.i:.j) = i `seq` j `seq` S.flatten make step Unknown $ mkStack x (Z:.i:.j-1) where
    make s = return $ mk y s
    step s
      | grd y j s = return $ S.Yield s (next y j s)
      | otherwise = return $ S.Done

--testZ i j = SPure.length $ mkStack (Z:.c:.c) (Z:.i:.j)
--{-# NOINLINE testZ #-}

infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}


dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}
