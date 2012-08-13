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

module ADP.Fusion.MultiArg where

import qualified Data.Vector.Fusion.Stream as S
import Data.Vector.Fusion.Stream.Size
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import Text.Printf
import GHC.Prim (Constraint(..))
import Debug.Trace


test1 = stack $ b ~~ r ~~ r ~~ b
--test2 = mapM_ print . take 500 . S.toList $ mkStream test1 (Z:.0:.6)
test2 = S.length $ mkStream test1 (Z:.0:.6)

class MkStream x where
  type XX x :: *
  type ST x :: *
  type SC x :: Constraint
  type SC x = ()
  mkStream :: SC x => x -> DIM2 -> S.Stream (ST x)
  mk   :: SC x => x -> Int -> XX x -> ST x
  step :: SC x => x -> Int -> ST x -> S.Step (ST x) (ST x)
  mk _ _ _ = undefined
  step _ _ _ = undefined
  {-# INLINE mk #-}
  {-# INLINE step #-}

instance MkStream Z where
  type XX Z = Z
  type ST Z = DIM1
  mkStream Z (Z:.i:.j) = S.singleton (Z:.i)
  {-# INLINE mkStream #-}

instance (MkStream y, SC y, ST y ~ Dim1 z) => MkStream (y :. Base) where
  type XX (y :. Base) = ST y
  type ST (y :. Base) = ST y :. Int
  type SC (y:.Base) = ()
  mkStream (y :. x) ij@(Z:.i:.j) = S.flatten (mk (y:.x) j) (step (y:.x) j) Unknown $ mkStream y ij
  mk yx j (z:.i) = (z:.i:.i+1)
  step yx j (z:.i:.k)
    | i+1==k && k <=j = S.Yield (z:.i:.k) (z:.i:.j+1)
    | otherwise       = S.Done
  {-# INLINE mkStream #-}
  {-# INLINE mk #-}
  {-# INLINE step #-}

instance (MkStream y, SC y, ST y ~ Dim1 z) => MkStream (y :. Region) where
  type XX (y :. Region) = ST y
  type ST (y :. Region) = ST y :. Int
  type SC (y:.Region) = Deep (y:.Region)
  mkStream (y :. x) ij@(Z:.i:.j) = S.flatten (mk (y:.x) j) (step (y:.x) j) Unknown $ mkStream y ij
  mk yx j (z:.i) = (z:.i:.i+1) where
    g = get yx (z:.i:.i+1)
  step yx j (z:.i:.k)
    | i+1<=k && k <=j && g<=2 = {- trace (printf "g: %d\n" g) $ -} S.Yield (z:.i:.k) (z:.i:.k+1)
    | otherwise       = S.Done
    where g = tot yx (z:.i:.i+1)
  {-# INLINE mkStream #-}
  {-# INLINE mk #-}
  {-# INLINE step #-}

class Deep x where
  get :: x -> ST x -> Int
  tot :: x -> ST x -> Int

instance Deep Z where
  get _ (Z:.i) = i
  tot _ _ = 0

instance Deep z => Deep (z:.Region) where
  get _ (_:.i) = i
  tot (z:._) (ii:.j) = tot z ii + (j - get z ii)

instance Deep z => Deep (z:.Base) where
  get _ (_:.i) = i
  tot (z:._) (ii:._) = tot z ii

type Dim1 z = z:.Int
type Dim2 z = Dim1 z :. Int
type Dim3 z = Dim2 z :. Int














infixr ~~
(~~) = (,)



class MkStack x where
  type Stack x :: *
  stack :: x -> Stack x

instance MkStack Base where
  type Stack Base = Z :. Base
  stack b = Z :. b

instance MkStack Region where
  type Stack Region = Z :. Region
  stack r = Z :. r

instance (MkStack y) => MkStack (x,y) where
  type Stack (x,y) = Stack y :. x
  stack (x,y) = stack y :. x

data Base = Base [Char]
  deriving (Show)

b = Base ['a' .. 'z']

data Region = Region [Char]

r = Region ['a'..'z']

