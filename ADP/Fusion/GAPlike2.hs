{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | 

module ADP.Fusion.GAPlike2 where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.Primitive
import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.Zero as UZ
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Text.Printf
import Data.List (intersperse)



class MkStream m x where
  type StreamConstraint x :: Constraint
  type StreamConstraint x = ()
  type StreamType x :: *
  mkStream      :: (StreamConstraint x) => x -> (Int,Int) -> S.Stream m (StreamType x)
  mkStreamInner :: (StreamConstraint x) => x -> (Int,Int) -> S.Stream m (StreamType x)



data ArgBottom = ArgBottom
  deriving (Show)

data AB = AB
  deriving (Show)

instance (Monad m) => MkStream m ArgBottom where
  type StreamType ArgBottom = AB:.(Int,())
  mkStream = mkStreamInner
  mkStreamInner ArgBottom (i,j) = S.singleton (AB:.(i,()))
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}



data Chr e = Chr (VU.Vector e)
  deriving (Show)

instance Build (Chr e) where
  type BuildStack (Chr e) = ArgBottom:.Chr e
  build c = ArgBottom:.c
  {-# INLINE build #-}

instance
  ( Monad m
  , MkStream m x
  , StreamConstraint x
  , StreamType x ~ (t0:.(Int,h0))
  , VU.Unbox e
  ) => MkStream m (x:.Chr e) where
  type StreamType (x:.Chr e) = StreamType x :. (Int,e)
  mkStream (x:.Chr cs) (i,j) = S.flatten mk step Unknown $ mkStream x (i,j-1) where
    mk (z:.(k,ka)) = return (z:.(k,ka):.j)
    step (z:.(k,ka):.l)
      | k+1==l && l==j = let c = VU.unsafeIndex cs k in c `seq` return $ S.Yield (z:.(k,ka):.(l,c)) (z:.(k,ka):.(j+1))
      | otherwise      = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  mkStreamInner (x:.Chr cs) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk (z:.(k,ka)) = return (z:.(k,ka):.k+1)
    step (z:.(k,ka):.l)
      | l<=j      = let c = VU.unsafeIndex cs k in c `seq` return $ S.Yield (z:.(k,ka):.(l,c)) (z:.(k,ka):.l+1)
      | otherwise = return $ S.Done
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}



instance Build (UZ.MArr0 s DIM2 e) where
  type BuildStack (UZ.MArr0 s DIM2 e) = ArgBottom:.MArr0 s DIM2 e
  build c = ArgBottom:.c
  {-# INLINE build #-}

instance
  ( Monad m
  , PrimMonad m
  , PrimState m ~ s
  , MkStream m x
  , StreamConstraint x
  , Prim e
  , StreamType x ~ (t0:.(Int,h0))
  ) => MkStream m (x:. UZ.MArr0 s DIM2 e) where
  type StreamType (x:. UZ.MArr0 s DIM2 e) = StreamType x :. (Int,e)
  mkStream (x:.pa) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk (z:.(k,ka)) = return (z:.(k,ka):.j)
    step (z:.(k,ka):.l)
      | k<l && l<=j = readM pa (Z:.k:.l) >>= \c -> c `seq` return $ S.Yield (z:.(k,ka):.(l,c)) (z:.(k,ka):.j+1)
      | otherwise   = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  mkStreamInner (x:.pa) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk (z:.(k,ka)) = return (z:.(k,ka):.k+1)
    step (z:.(k,ka):.l)
      | l<=j      = readM pa (Z:.k:.l) >>= \c -> c `seq` return $ S.Yield (z:.(k,ka):.(l,c)) (z:.(k,ka):.l+1)
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}



-- * Build

class Build x where
  type BuildStack x :: *
  build :: x -> BuildStack x

instance Build x => Build (x,y) where
  type BuildStack (x,y) = BuildStack x :. y
  build (x,y) = build x :. y
  {-# INLINE build #-}



-- * combinators

infixl 8 <<<
(<<<) f t ij = S.map (\(_,za) -> apply f za) $ mkStream (build t) ij
{-# INLINE (<<<) #-}

infixl 7 |||
(|||) xs ys ij = xs ij S.++ ys ij
{-# INLINE (|||) #-}

infixl 6 ...
(...) s h ij = h $ s ij
{-# INLINE (...) #-}

infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}

infixl 9 %
(%) = (,)
{-# INLINE (%) #-}



-- * Apply

class Apply x where
  type Fun x :: *
  apply :: Fun x -> x


instance Apply (AB:.(Int,())) where
  Fun (f -> (AB:.(Int,()))) = (f -> f)
  apply f _ = f

instance Apply x => Apply (x:.(Int,y)) where
  apply f (xs:.(_,y)) = (apply f xs) y

{-
mkApply :: Char -> IO ()
mkApply to = do
  let xs = ['a' .. to]
  let zs :: String = concatMap (printf ":.(Int,%c)") xs
  let as :: String = concatMap (printf "%c -> ") $ xs
  let fs :: String = concatMap (printf "%c ") $ xs
  printf "instance Apply (AB:.(Int,())%s -> res) where\n" zs
  printf "  type  Fun (AB:.(Int,())%s -> res) = %sres\n" zs as
  printf "  apply fun (_:._%s) = fun %s\n" zs fs
  printf "  {-# INLINE apply #-}\n"
-}








-- * Criterion tests

testM3 :: Int -> Int -> Int
testM3 i j = runST doST where
  doST :: ST s Int
  doST = do
    s :: UZ.MArr0 s DIM2 Int <- fromAssocsM (Z:.0:.0) (Z:.j:.j) 0 []
    S.length $ mkStream (ArgBottom:.s:.s:.s) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testM3 #-}

testM4 :: Int -> Int -> Int
testM4 i j = runST doST where
  doST :: ST s Int
  doST = do
    s :: UZ.MArr0 s DIM2 Int <- fromAssocsM (Z:.0:.0) (Z:.j:.j) 0 []
    S.length $ mkStream (ArgBottom:.s:.s:.s:.s) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testM4 #-}

