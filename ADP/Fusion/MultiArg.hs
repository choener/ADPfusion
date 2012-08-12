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

module ADP.Fusion.MultiArg where

import qualified Data.Vector.Fusion.Stream as S
import Data.Vector.Fusion.Stream.Size
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import Text.Printf


test1 = stack $ b ~~ r ~~ r ~~ b
test2 = mapM_ print . take 500 . S.toList $ mkStreamLast test1 (Z:.0:.6)

class MkStream x where
  type ST x :: *
  mkStream :: x -> DIM2 -> S.Stream (ST x)
  mkStreamLast :: x -> DIM2 -> S.Stream (ST x)

-- | the base of recursion leads to just Z:.i

instance MkStream Z where
  type ST Z = DIM1
  mkStream Z (Z:.i:.j) = S.singleton (Z:.i)
  mkStreamLast = mkStream

-- | each additional element adds one to the stack

instance (MkStep x, MkStream y, ST y ~ Dim1 z) => MkStream (y :. x) where
  type ST (y :. x) = ST y :. Int
  mkStream (y :. x) ij@(Z:.i:.j) = S.flatten (mk x j) (step x j) Unknown $ mkStream y ij
  mkStreamLast (y :. x) ij@(Z:.i:.j) = case isConst x of
    Just c  -> S.flatten (mkLast x j) (stepLast x j) Unknown $ mkStreamLast y (Z:.i:.j-c)
    Nothing -> S.flatten (mkLast x j) (stepLast x j) Unknown $ mkStream y ij

class MkStep x where
  mk,mkLast :: x -> Int -> Dim1 z -> Dim2 z
  step,stepLast :: x -> Int -> Dim2 z -> S.Step (Dim2 z) (Dim2 z)
  isConst :: x -> Maybe Int

instance MkStep Base where
  mk _ j (z:.i) = (z:.i:.i+1)
  mkLast = mk
  step _ j (z:.i:.k)
    | i+1==k && k <=j = S.Yield (z:.i:.k) (z:.i:.j+1)
    | otherwise       = S.Done
  stepLast _ j (z:.i:.k)
    | i+1==k && k==j = S.Yield (z:.i:.k) (z:.i:.j+1)
    | otherwise      = S.Done
  isConst _ = Just 1

instance MkStep Region where
  mk _ j (z:.i) = (z:.i:.i+1)
  mkLast _ j (z:.i) = let k = max (i+1) j in (z:.i:.k)
  step _ j (z:.i:.k)
    | k<=j    = S.Yield (z:.i:.k) (z:.i:.k+1)
    | otherwise = S.Done
  stepLast _ j (z:.i:.k)
    | k<=j    = S.Yield (z:.i:.k) (z:.i:.k+1)
    | otherwise = S.Done
  isConst _ = Nothing

type Dim1 z = z:.Int
type Dim2 z = Dim1 z :. Int
type Dim3 z = Dim2 z :. Int



infixr ~~
(~~) = (,)

infixr :~~
data (:~~) a b = a :~~ b deriving (Show)

data Y a = Y a deriving (Show)


class MkStack x where
  type Stack x :: *
  stack :: x -> Stack x

instance MkStack Base where
  type Stack Base = Z :. Base -- Base :~~ Z
  stack b = Z :. b -- b :~~ Z

instance MkStack Region where
  type Stack Region = Z :. Region
  stack r = Z :. r

instance (MkStack y) => MkStack (x,y) where
  type Stack (x,y) = Stack y :. x -- x :~~ Stack y
  stack (x,y) = stack y :. x -- x :~~ stack y

data Base = Base [Char]
  deriving (Show)

b = Base ['a' .. 'z']

data Region = Region [Char]

r = Region ['a'..'z']


-- iloop <<< bp ~~ r30 ~~ pb ~~ stem ~~ bp ~~ r30 ~~ pb
-- mloop <<< bp ~~ m1 ~~ m ~~ pb
