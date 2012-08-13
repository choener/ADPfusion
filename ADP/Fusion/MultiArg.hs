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


test1 = stack $ b ~~ lr ~~ r ~~ lr ~~ b
{-# INLINE test1 #-}
--test2 = mapM_ print . take 500 . S.toList $ mkStream test1 (Z:.0:.50)
test2 = S.length $ mkStream test1 (Z:.0:.50)
{-# NOINLINE test2 #-}

class MkStream x where
  type LeftIdx x :: *
  type NewIdx x :: *
  type StreamConstraint x :: Constraint
  type StreamConstraint x = ()
  mkStream :: StreamConstraint x => x -> DIM2 -> S.Stream (NewIdx x)
  mk   :: StreamConstraint x => x -> Int -> LeftIdx x -> NewIdx x
  step :: StreamConstraint x => x -> Int -> NewIdx x -> S.Step (NewIdx x) (NewIdx x)
  mk _ _ _ = undefined
  step _ _ _ = undefined
  {-# INLINE mk #-}
  {-# INLINE step #-}

instance MkStream Z where
  type LeftIdx Z = Z
  type NewIdx Z = DIM1
  mkStream Z (Z:.i:.j) = S.singleton (Z:.i)
  {-# INLINE mkStream #-}

instance (MkStream y, StreamConstraint y, NewIdx y ~ Dim1 z) => MkStream (y :. Base) where
  type LeftIdx (y :. Base) = NewIdx y
  type NewIdx (y :. Base) = NewIdx y :. Int
  type StreamConstraint (y:.Base) = ()
  mkStream (y :. x) ij@(Z:.i:.j) = S.flatten (mk (y:.x) j) (step (y:.x) j) Unknown $ mkStream y ij
  mk yx j (z:.i) = (z:.i:.i+1)
  step yx j (z:.i:.k)
    | i+1==k && k <=j = S.Yield (z:.i:.k) (z:.i:.j+1)
    | otherwise       = S.Done
  {-# INLINE mkStream #-}
  {-# INLINE mk #-}
  {-# INLINE step #-}

instance (MkStream y, StreamConstraint y, NewIdx y ~ Dim1 z) => MkStream (y :. Region) where
  type LeftIdx (y :. Region) = NewIdx y
  type NewIdx (y :. Region) = NewIdx y :. Int
  type StreamConstraint (y:.Region) = ()
  mkStream (y :. x) ij@(Z:.i:.j) = S.flatten (mk (y:.x) j) (step (y:.x) j) Unknown $ mkStream y ij
  mk yx j (z:.i) = (z:.i:.i+1)
  step yx j (z:.i:.k)
    | i+1<=k && k <=j = S.Yield (z:.i:.k) (z:.i:.k+1)
    | otherwise       = S.Done
  {-# INLINE mkStream #-}
  {-# INLINE mk #-}
  {-# INLINE step #-}

instance (MkStream y, StreamConstraint y, NewIdx y ~ Dim1 z) => MkStream (y :. LRegion) where
  type LeftIdx (y :. LRegion) = NewIdx y
  type NewIdx (y :. LRegion) = NewIdx y :. Int
  type StreamConstraint (y:.LRegion) = Deep (y:.LRegion)
  mkStream (y :. x) ij@(Z:.i:.j) = S.flatten (mk (y:.x) j) (step (y:.x) j) Unknown $ mkStream y ij
  mk _ j (z:.i) = (z:.i:.i+1)
  step yx j (z:.i:.k)
    | i+1<=k && k <=j && g<=10 = {- trace (printf "g: %d\n" g) $ -} S.Yield (z:.i:.k) (z:.i:.k+1)
    | otherwise       = S.Done
    where g = tot yx (z:.i:.i+1)
  {-# INLINE mkStream #-}
  {-# INLINE mk #-}
  {-# INLINE step #-}

class Deep x where
  get :: x -> NewIdx x -> Int
  tot :: x -> NewIdx x -> Int

instance Deep Z where
  get _ (Z:.i) = i
  tot _ _ = 0
  {-# INLINE get #-}
  {-# INLINE tot #-}

instance Deep z => Deep (z:.LRegion) where
  get _ (_:.i) = i
  tot (z:._) (ii:.j) = tot z ii + (j - get z ii)
  {-# INLINE get #-}
  {-# INLINE tot #-}

instance Deep z => Deep (z:.Region) where
  get _ (_:.i) = i
  tot (z:._) (ii:._) = tot z ii
  {-# INLINE get #-}
  {-# INLINE tot #-}

instance Deep z => Deep (z:.Base) where
  get _ (_:.i) = i
  tot (z:._) (ii:._) = tot z ii
  {-# INLINE get #-}
  {-# INLINE tot #-}



type Dim1 z = z:.Int
type Dim2 z = Dim1 z :. Int
type Dim3 z = Dim2 z :. Int














infixr ~~
(~~) = (,)
{-# INLINE (~~) #-}



class MkStack x where
  type Stack x :: *
  stack :: x -> Stack x

instance MkStack Base where
  type Stack Base = Z :. Base
  stack b = Z :. b
  {-# INLINE stack #-}

instance MkStack Region where
  type Stack Region = Z :. Region
  stack r = Z :. r
  {-# INLINE stack #-}

instance (MkStack y) => MkStack (x,y) where
  type Stack (x,y) = Stack y :. x
  stack (x,y) = stack y :. x
  {-# INLINE stack #-}

data Base = Base [Char]
  deriving (Show)

b = Base ['a' .. 'z']

data Region = Region [Char]

r = Region ['a'..'z']

data LRegion = LRegion [Char]

lr = LRegion ['a'..'z']

