{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The "GAP-like" version of ADPfusion. We now encode arguments as distinct
-- data types. The 'MkStream' type class determines the creation of streams.

module ADP.Fusion.GAPlike where

import ADP.Fusion.Monadic.Internal (Apply(..))
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Char
import Data.Primitive
import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.Zero
import Data.Vector.Fusion.Stream.Size
import Debug.Trace
import GHC.Prim (Constraint(..))
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import qualified Data.Vector.Fusion.Stream as SPure
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Text.Printf



-- *

type family   TopIdx x :: *

type family   TopArg x :: *

class (Monad m) => MkStream m x where
  type SC x :: Constraint
  type SC x = ()
  -- | The outer stream generator.
  mkStream      :: (SC x) => x -> DIM2 -> S.Stream m (TopIdx x, TopArg x)
  mkStreamInner :: (SC x) => x -> DIM2 -> S.Stream m (TopIdx x, TopArg x)

type StepType m x y
  =  (TopIdx x:.TopIdx y, TopArg x)
  -> m (S.Step (TopIdx x:.TopIdx y, TopArg x) (TopIdx x:.TopIdx y, TopArg x:.TopArg y))

type MkType m x y
  =  (TopIdx x, TopArg x)
  -> m (TopIdx x:.TopIdx y, TopArg x)

class Build x where
  type Bld x :: *
  build :: x -> Bld x

-- ** Stack TopIdx / TopArg

type instance TopIdx (x:.y) = TopIdx x :. TopIdx y

type instance TopArg (x:.y) = TopArg x :. TopArg y

instance Build x => Build (x,y) where
  type Bld (x,y) = Bld x :. y
  build (a,b) = build a :. b
  {-# INLINE build #-}



-- ** Stream generation for the bottom of the argument stack.

type instance TopIdx Z = Z:.Int

type instance TopArg Z = Z

instance (Monad m) => MkStream m Z where
  mkStream = mkStreamInner
  mkStreamInner Z (Z:.i:.j) = S.unfoldr step i where
    step i
      | i<=j      = Just ((Z:.i, Z), (j+1))
      | otherwise = Nothing
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}



-- ** Stream generation for our typical two-dimensional tables.

type instance TopIdx (MArr0 s DIM2 elm) = Int

type instance TopArg (MArr0 s DIM2 elm) = elm

instance Build (MArr0 s DIM2 elm) where
  type Bld (MArr0 s DIM2 elm) = Z:.MArr0 s DIM2 elm
  build a = Z:.a
  {-# INLINE build #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, Prim elm, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.MArr0 s DIM2 elm) where
  type SC (x:.MArr0 s DIM2 elm) = ()
  -- | If this is an outermost stream, create only one element with size
  -- '[k,j]'. The recursive stream generation then switches to 'mkStreamInner'.
  mkStream (x:.marr) (Z:.i:.j) = S.flatten mk step Unknown $ mkStreamInner x (Z:.i:.j) where
    mk :: MkType m x (MArr0 s DIM2 elm)
    mk (zi:.k,za) = return $ (zi:.k:.k,za)
    step :: StepType m x (MArr0 s DIM2 elm)
    step (zi:.k,za)
      | k<=j      = do c <- readM marr (Z:.k:.j)
                       return $ S.Yield (zi:.k,za:.c) (zi:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}
  -- | Inner streams advance by one from one step to the next.
  mkStreamInner (x:.marr) (Z:.i:.j) = S.flatten mk step Unknown $ mkStreamInner x (Z:.i:.j) where
    mk :: MkType m x (MArr0 s DIM2 elm)
    mk (zi:.k,za) = return $ (zi:.k:.k,za)
    step :: StepType m x (MArr0 s DIM2 elm)
    step (zi:.k,za)
      | k<=j      = do c <- readM marr (Z:.k:.j)
                       return $ S.Yield (zi:.k,za:.c) (zi:.k+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStreamInner #-}



-- ** A terminal symbol with a width of 1. The underlying input is stored in a
-- primitive array 'Arr0' of dimension one ('DIM1'). The element type 'elm' is
-- variable.

-- | A terminal symbol 'PAsingle' of width 1.

data PAsingle elm = PAsingle !(Arr0 DIM1 elm)

type instance TopIdx (PAsingle elm) = Int

type instance TopArg (PAsingle elm) = elm

instance Build (PAsingle elm) where
  type Bld (PAsingle elm) = Z:.PAsingle elm
  build a = Z:.a
  {-# INLINE build #-}

instance (Monad m, Prim elm, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.PAsingle elm) where
  type SC (x:.PAsingle elm) = ()
  -- | We are still in the outer stream and have only encountered constant-size
  -- arguments. We handle this single argument and decrease the constant width
  -- of the remaining (left) arguments.
  mkStream (x:.PAsingle arr) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j-1) where
    -- | Set the local width to [j-1,j].
    mk :: MkType m x (PAsingle elm)
    mk (zi,za) = return $ (zi:.j-1,za)
    -- | If 'i>=k' we have a valid region of size [j-1,j] ('mk').
    step :: StepType m x (PAsingle elm)
    step (zi:.k,za)
      | i>=k      = do let c = arr ! (Z:.k)
                       return $ S.Yield (zi:.k,za:.c) (zi:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}
  -- | We can not decrease 'j' anymore, as we could well be within moving
  -- indices.
  mkStreamInner (x:.PAsingle arr) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    -- | Create a new width of size [k,k+1]
    mk :: MkType m x (PAsingle elm)
    mk (zi:.k,za) = return $ (zi:.k:.k+1,za)
    -- | Do a step of size 1 [k,k+1], then finish.
    step :: StepType m x (PAsingle elm)
    step (zi:.k,za)
      | k<=j      = do let c = arr ! (Z:.k)
                       return $ S.Yield (zi:.k,za:.c) (zi:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStreamInner #-}



infix 8 <<<
(<<<) f t ij = S.map (\(_,za) -> apply f za) $ mkStream (build t) ij
{-# INLINE (<<<) #-}

infix 7 ...
(...) s h ij = h $ s ij
{-# INLINE (...) #-}


infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}

infixl 9 %
(%) = (,)
{-# INLINE (%) #-}

testST :: PAsingle Char -> Int -> Int -> Int
testST inp i j = runST $ embedST inp i j
{-# NOINLINE testST #-}

embedST :: PAsingle Char -> Int -> Int -> ST s Int
embedST inp i j = do
  vm :: VUM.MVector s Int <- VUM.replicate 10 0
  vn :: VUM.MVector s Int <- VUM.replicate 10 0
  tbl :: MArr0 s DIM2 Int <- fromAssocsM (Z:.0:.0) (Z:.10:.10) 0 []
  -- (fcic <<< inp % tbl % inp ... (S.foldl' (+) 0)) (Z:.i:.j)
  gST (fcic, (S.foldl' (+) 0)) inp tbl (Z:.i:.j)
{-# NOINLINE embedST #-}

fcic :: Char -> Int -> Char -> Int
fcic l x r = ord l + x + ord r
-- {-# INLINE fcic #-}

-- a simple test grammar

gST (fcic, h) inp tbl =
  ( (fcic <<< inp % tbl % inp ... h)
  )
{-# INLINE gST #-}

{-
 - This is how it should look like in the future, 'tbl' is defined by the rules
 - to the right.
 -
gST (fcic, h) inp tbl =
  ( ( tbl, fcic <<< inp % tbl % inp ... h )
  )
-}



-- test stuff

{-

-- **

type instance TopIdx (VUM.MVector s elm) = Int

type instance TopArg (VUM.MVector s elm) = elm

instance (Monad m, PrimMonad m, VUM.Unbox elm, PrimState m ~ s, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.VUM.MVector s elm) where
  type SC (x:.VUM.MVector s elm) = ()
  mkStream (x:.mvec) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk :: MkType m x (VUM.MVector s elm)
    mk (zi:.k,za) = return $ (zi:.k:.k, za)
    step :: StepType m x (VUM.MVector s elm)
    step (zi:.k,za)
      | k<=j      = do  c <- VUM.unsafeRead mvec k
                        return $ S.Yield (zi:.k,za:.c) (zi:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

instance Build (VUM.MVector s elm) where
  type Bld (VUM.MVector s elm) = Z:.VUM.MVector s elm
  build a = Z:.a
  {-# INLINE build #-}

-}



{-
instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.Chr) where
  type SC (x:.Chr) = ()
  mkStream (x:.Chr cs) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zi,za) = let (_:.k) = zi in return (zi:.k, za)
    step :: StepType m x Chr
    step (zi,za)
      | k<=j      = c `seq` return $ S.Yield (zi,za:.c) (zi':.j+1,za)
      | otherwise = return $ S.Done
      where (zi':.k) = zi
            c        = VU.unsafeIndex cs k
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.Dhr) where
  type SC (x:.Dhr) = ()
  mkStream (x:.Dhr ds) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zi:.k,za) = return $ (zi:.k:.k, za)
    step :: StepType m x Dhr
    step (zi:.k,za)
      | k<=j      = do  let c = ds ! (Z:.k)
                        return $ S.Yield (zi:.k,za:.c) (zi:.j+1,za)
      | otherwise = return $ S.Done
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

instance Build Chr where
  type Bld Chr = Z:.Chr
  build a = Z:.a
  {-# INLINE build #-}

instance Build LR where
  type Bld LR = Z:.LR
  build a = Z:.a

dvu = VU.fromList . concat $ replicate 1000 ['a' .. 'z']
{-# NOINLINE dvu #-}

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

testZ i j = SPure.length $ mkStream (Z:.ccc) (Z:.i:.j)
{-# NOINLINE testZ #-}

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

fiicii :: Int -> Int -> Char -> Int -> Int -> Int
fiicii i j c k l = i+j+k+l + ord c
{- INLINE fiicii #-}

cv :: Char -> Int -> Int
cv c i = case c of
  'A' -> 1+i
  _   -> 2+i
{-# INLINE cv #-}

instance (Monad m, MkStream m x, SC x, TopIdx x ~ (t0:.Int)) => MkStream m (x:.LR) where
  type SC (x:.LR) = (Get x)
  mkStream (x:.LR limit lr) (Z:.i:.j) = S.flatten mk step Unknown $ mkStream x (Z:.i:.j) where
    mk (zi:.k,za) = return $ (zi:.k:.k, za)
    step :: StepType m x LR
    step (zi:.k,za)
      | k<=j && dd <= limit = do  let c = VU.unsafeIndex lr k
                                  return $ S.Yield (zi:.k,za:.c) (zi:.j+1,za)
      | otherwise = return $ S.Done
      where dd = down (x,zi)
    {-# INLINE [0] mk #-}
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

type instance TopIdx Chr = Int
type instance TopIdx Dhr = Int
type instance TopIdx LR = Int
type instance TopArg Chr = Char
type instance TopArg Dhr = Char
type instance TopArg LR = Int

instance XYZ x => XYZ (x:.LR) where
  rofl (x:._,zi:._) = 1 + rofl (x,zi)
  {-# INLINE rofl #-}

instance XYZ x => XYZ (x:.Dhr) where
  rofl (x:._,zi:._) = 1 + rofl (x,zi)
  {-# INLINE rofl #-}

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

class DS x where
  ds :: x -> y -> y

instance DS Z where
  ds Z a = a
  {-# INLINE ds #-}

instance DS x => DS (x:.y) where
  ds (x:.y) a = ds x (y `seq` a)
  {-# INLINE ds #-}

class XYZ x where
  rofl :: (x, TopIdx x) -> Int

instance XYZ Z where
  rofl _ = 0
  {-# INLINE rofl #-}

instance XYZ x => XYZ (x:.VUM.MVector s elm) where
  rofl (x:._,zi:._) = 1 + rofl (x,zi)
  {-# INLINE rofl #-}

class Get x where
  getI :: (x, TopIdx x) -> Int
  down :: (x, TopIdx x) -> Int

instance Get Z where
  getI (_,zi:.k) = k
  down _          = 0
  {-# INLINE getI #-}
  {-# INLINE down #-}

instance Get x => Get (x:.VUM.MVector s elm) where
  getI (_,_:.k) = k
  down (x:._,zi:._) = down (x,zi)
  {-# INLINE getI #-}
  {-# INLINE down #-}

-}



