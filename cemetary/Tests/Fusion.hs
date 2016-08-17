{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Tests.Fusion where

import Control.Applicative
import Data.Array.Repa.Index
import Data.Array.Repa.Shape
import Data.Array.Repa.Arbitrary
import Debug.Trace
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import Test.QuickCheck
import Test.QuickCheck.All
import Test.QuickCheck.Monadic
import Data.List ((\\))
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion



mkFlattening :: Int
mkFlattening = S.foldl' (+) 0 $ S.flatten mk1 step1 Unknown $ S.flatten mk1 step1 Unknown $ S.flatten mk1 step1 Unknown $ S.enumFromStepN 1 1 10
  where mk1 i = S.enumFromStepN i 1 11
        step1 (SM.Stream go x !z) = case (unId $ go x) of
          S.Done -> S.Done
          S.Skip y -> S.Skip (SM.Stream go y z)
          S.Yield a y -> S.Yield a (SM.Stream go y z)
        {-# INLINE [1] mk1   #-}
        {-# INLINE [1] step1 #-}
{-# NOINLINE mkFlattening #-}


ccm :: Monad m => (a -> SM.Stream m b) -> SM.Stream m a -> SM.Stream m b
ccm gen = SM.flatten mk step Unknown
  where mk = return . gen
        step (SM.Stream go x _) = do
          s <- go x
          case s of
            SM.Done      -> return $ SM.Done
            SM.Skip y    -> return $ SM.Skip (SM.Stream go y Unknown)
            SM.Yield b y -> return $ SM.Yield b (SM.Stream go y Unknown)
        {-# INLINE [1] mk   #-}
        {-# INLINE [1] step #-}
{-# INLINE ccm #-}

fooboo :: Int
fooboo = S.foldl' (+) 0 $ ccm (\i -> S.enumFromStepN i 1 11) $ ccm (\i -> S.enumFromStepN i 1 11) $ ccm (\i -> S.enumFromStepN i 1 11) $ S.enumFromStepN 1 1 10
{-# NOINLINE fooboo #-}

oriboo :: Int
oriboo = S.foldl' (+) 0 $ S.concatMap (\i -> S.enumFromStepN i 1 11) $ S.concatMap (\i -> S.enumFromStepN i 1 11) $ S.concatMap (\i -> S.enumFromStepN i 1 11) $ S.enumFromStepN 1 1 10
{-# NOINLINE oriboo #-}


{-
testF :: Int -> Int -> Int
testF i j =
  p6 <<< peekL testVs % chr testVs % Tbl testA % sregion 3 10 testVs % chr testVs % peekR testVs |||
  p6 <<< peekR testVs % chr testVs % Tbl testA % sregion 3 10 testVs % chr testVs % peekL testVs ... (S.foldl' (+) 0) $ subword i j
{-# NOINLINE testF #-}

p6 a b c d e f = a+b+c+ VU.maximum d +e+f

{-
testG :: Int -> Int -> Int
testG i j =
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs |||
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs ... (Sp.foldl' (+) 0) $ subword i j
{-# NOINLINE testG #-}
-}

testA :: PA.Unboxed (Z:.Subword) Int
testA = PA.fromAssocs (Z:.subword 0 0) (Z:.subword 0 50) 0 []
{-# NOINLINE testA #-}

testVs :: VU.Vector Int
testVs = VU.fromList [ 0 .. 9999 ]
{-# NOINLINE testVs #-}

{-
--gugg :: Int -> Int -> [(Int,VU.Vector Int,Int)]
gugg i j = (,,) <<< chrR testVs % region testVs % chrL testVs ... Sp.toList $ subword i j
-}
-}

