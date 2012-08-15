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


{-
test1 = stack $ b ~~r  ~~ r ~~ b -- ~~ lr ~~ r ~~ lr ~~ b
{-# INLINE test1 #-}
--test2 = mapM_ runTest2 [0..10]
--test2 :: Int -> Int -> Int
test2 :: Int -> Int -> Int
test2 i j = (brrb <<< test1 ... (SPure.foldl' (+) 0)) (Z:.i:.j)
{-# NOINLINE test2 #-}
-}

infixl 8 <<<
(<<<) f t ij = S.map (\(_,_,c) -> apply f c) $ mkStreamLast (stack t) ij
{-# INLINE (<<<) #-}

infixl 7 |||
(|||) xs ys ij = xs ij S.++ ys ij
{-# INLINE (|||) #-}

infixl 6 ...
(...) stream h ij = h $ stream ij
{-# INLINE (...) #-}

{-
brrb b1 r1 r2 b2 = ord b1 + r1 + r2 + ord b2
{-# INLINE brrb #-}

runTest2 k = do
  putStrLn ""
  print (Z:.0:.k)
  mapM_ print . take 500 . SPure.toList $ ((,,,) <<< test1) (Z:.0:.k)
-}

class (Monad m) => MkStream m x where
  -- indices
  type LeftIdx x :: *
  type NewIdx x  :: *
  -- argument indices
  type LeftAdx x :: *
  type NewAdx x  :: *
  --
  type LeftArg x :: *
  type NewArg x  :: *
  --
  type StreamConstraint x t :: Constraint
  mkStream, mkStreamLast :: (t ~ NewIdx x, StreamConstraint x t) => x -> DIM2 -> S.Stream m (t,NewAdx x, NewArg x)
  mk, mkLast             :: (t ~ NewIdx x, StreamConstraint x t) => x -> Int -> (LeftIdx x, LeftAdx x, LeftArg x) -> m (t, LeftAdx x, LeftArg x)
  step, stepLast         :: (t ~ NewIdx x, StreamConstraint x t) => x -> Int -> (t, LeftAdx x, LeftArg x) -> m (S.Step (t, LeftAdx x, LeftArg x) (t, LeftAdx x, LeftArg x))

instance (Monad m) => MkStream m Z where
  --
  type LeftIdx Z = Z
  type NewIdx  Z = Z:.Index Z
  --
  type LeftAdx Z = Z
  type NewAdx  Z = Z
  --
  type LeftArg Z = Z
  type NewArg  Z = Z
  --
  type StreamConstraint Z t = ()
  mkStream Z (Z:.i:.j) = S.singleton (Z:.I i, Z, Z)
  mkStreamLast = mkStream
  mk       = error "MkStream Z/mk: should never be called"
  mkLast   = error "MkStream Z/mkLast: should never be called"
  step     = error "MkStream Z/step: should never be called"
  stepLast = error "MkStream Z/stepLast: should never be called"
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamLast #-}

instance (Monad m, MkStream m y, StreamConstraint y (NewIdx y), (NewIdx y) ~ (t0 :. Index t1)) => MkStream m (y :. Base) where
  --
  type LeftIdx (y :. Base) = NewIdx y
  type NewIdx  (y :. Base) = NewIdx y :. Index Base
  --
  type LeftAdx (y :. Base) = NewAdx y
  type NewAdx  (y :. Base) = NewAdx y :. Z
  --
  type LeftArg (y :. Base) = NewArg y
  type NewArg  (y :. Base) = NewArg y :. Char
  --
  type StreamConstraint (y:.Base) t = ()  -- (Deep t)
  mkStream     yx@(y:.Base cs) ij@(Z:.i:.j) = S.map (\(i,a,v) -> let (_:.I k:._) = i in (i,a:.Z,v:.cs `VU.unsafeIndex` k))
                                            . S.flatten (mk yx j)     (step yx j)     Unknown
                                            $ mkStream     y ij
  mkStreamLast yx@(y:.Base cs) ij@(Z:.i:.j) = S.map (\(i,a,v) -> let (_:.I k:._) = i in (i,a:.Z,v:.cs `VU.unsafeIndex` k))
                                            . S.flatten (mkLast yx j) (stepLast yx j) Unknown
                                            $ mkStreamLast y (Z:.i:.j-1)
  mk _ _ (zi@(z:.I i),adx,vs) = return ((zi:.I (i+1)),adx,vs)
  mkLast = mk
  step _ j ((z:.I i:.I k),adx,vs)
    | k<=j      = return $ S.Yield ((z:.I i:.I k),adx,vs) ((z:.I i:. I (j+1)),adx,vs)
    | otherwise = return $ S.Done
  stepLast _ j ((z:.I i:.I k),adx,vs)
    | k==j      = return $ S.Yield ((z:.I i:.I k),adx,vs) ((z:.I i:. I (j+1)),adx,vs)
    | otherwise = return $ S.Done
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamLast #-}
  {-# INLINE mk #-}
  {-# INLINE mkLast #-}
  {-# INLINE step #-}
  {-# INLINE stepLast #-}

instance (Monad m, MkStream m y, StreamConstraint y (NewIdx y), (NewIdx y) ~ (t0 :. Index t1)) => MkStream m (y :. Region) where
  --
  type LeftIdx (y :. Region) = NewIdx y
  type NewIdx  (y :. Region) = NewIdx y :. Index Region
  --
  type LeftAdx (y :. Region) = NewAdx y
  type NewAdx  (y :. Region) = NewAdx y :. Z
  --
  type LeftArg (y :. Region) = NewArg y
  type NewArg  (y :. Region) = NewArg y :. Int
  --
  type StreamConstraint (y:.Region) t = ()
  mkStream     yx@(y:.Region cs) ij@(Z:.i:.j) = S.map (\(i,a,v) -> let (_:.I k:.I j) = i in (i,a:.Z,v:.(j-k)))
                                              . S.flatten (mk yx j)     (step yx j)     Unknown
                                              $ mkStream y ij
  mkStreamLast yx@(y:.Region cs) ij@(Z:.i:.j) = S.map (\(i,a,v) -> let (_:.I k:.I j) = i in (i,a:.Z,v:.(j-k)))
                                              . S.flatten (mkLast yx j) (stepLast yx j) Unknown
                                              $ mkStream y ij
  mk     _ _ (zi@(z:.I i),adx,vs) = return ((zi:.I i),adx,vs)
  mkLast _ j (zi,adx,vs)          = return ((zi:.I j),adx,vs)
  step _ j (zik@(z:.I i:.I k),adx,vs)
    | k<=j      = return $ S.Yield ((z:.I i:.I k),adx,vs) ((z:.I i:. I (k+1)),adx,vs)
    | otherwise = return $ S.Done
  stepLast = step
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamLast #-}
  {-# INLINE mk #-}
  {-# INLINE mkLast #-}
  {-# INLINE step #-}
  {-# INLINE stepLast #-}

newtype Index t = I Int
  deriving (Show)

class Deep t where
  get :: t -> Int
  down :: t -> Int

instance Deep (Z:.Index Z) where
  get (z:.I i) = i
  down (z:.I i) = i
  {-# INLINE get #-}
  {-# INLINE down #-}

instance Deep y => Deep (y:.Index Base) where
  get (z:.I i) = i
  down (z:.I i) = down z + (i - get z)
  {-# INLINE get #-}
  {-# INLINE down #-}

instance Deep y => Deep (y:.Index Region) where
  get (z:.I i) = i
  down (z:.I i) = i
  {-# INLINE get #-}
  {-# INLINE down #-}











type Dim1 z = z:.Int
type Dim2 z = Dim1 z :. Int
type Dim3 z = Dim2 z :. Int

infixl 9 ~~
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

instance (MkStack y) => MkStack (y,x) where
  type Stack (y,x) = Stack y :. x
  stack (y,x) = stack y :. x
  {-# INLINE stack #-}

data Base = Base (VU.Vector Char)

instance Show Base where
  show _ = "Base"

b = Base dvu

data Region = Region (VU.Vector Char)

instance Show Region where
  show _ = "Region"

r = Region dvu

data LRegion = LRegion [Char]

lr = LRegion ['a'..'z']


dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}
