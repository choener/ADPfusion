{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

-- | Very small ADPfusion-like systems to evaluate performance characteristics.

module Main where

import qualified Data.Vector.Fusion.Stream as S
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Generic as VG
import           Criterion.Main
import           Data.Vector.Unboxed.Deriving
import qualified Data.Vector.Generic
import qualified Data.Vector.Generic.Mutable
import qualified GHC.Exts as GHC
import qualified GHC.Base as GHC
import           Unsafe.Coerce
import           Data.Word
import           GHC.Types
import           GHC.Prim

-- we need these three lines from repa

infixl 3 :.
data (:.) a b = !a :. !b
data Z = Z

{-# NOINLINE v #-}
v :: VU.Vector Int
v = VU.fromList [1..1004]

data ABCD = A | B | C | D
  deriving (Show,Eq,Bounded,Ord,Enum)

derivingUnbox "ABCD"
  [t| ABCD -> Int |]
  [| fromEnum |]
  [| toEnum   |]

w :: VU.Vector ABCD
w = VU.fromList $ concat $ replicate 251 [A .. D]

data Var x = Var (VU.Vector x)
  deriving (Show)


{-# NOINLINE partial3 #-}
partial3 :: Int -> Int -> Int
partial3 i j = S.foldl' min maxBound
             $ S.map (\(Z:.a:.b:.c) -> a+b+c)
             $ S.map partialElems
             $ partialIndex (Z:.Var v:.Var v:.Var v) i j

{-# NOINLINE partial5 #-}
partial5 :: Int -> Int -> Int
partial5 i j = S.foldl' min maxBound
             $ S.map (\(Z:.a:.b:.c:.d:.e) -> a+b+c+d+e)
             $ S.map partialElems
             $ partialIndex (Z:.Var v:.Var v:.Var v:.Var v:.Var v) i j


class PartialIndex p where
  data E  p :: *
  type PE p :: *
  partialElems :: E p -> PE p
  getIndex     :: E p -> Int
  partialIndex :: p -> Int -> Int -> S.Stream (E p)

instance PartialIndex Z where
  data E  Z = EZ !Int
  type PE Z = Z
  partialElems _ = Z
  getIndex (EZ k) = k
  partialIndex _ i _ = S.singleton (EZ i)
  {-# INLINE partialElems #-}
  {-# INLINE getIndex #-}
  {-# INLINE partialIndex #-}

instance (VU.Unbox v, PartialIndex z) => PartialIndex (z:.Var v) where
  data E  (z:.Var v) = EzVar !Int !(E z) !v
  type PE (z:.Var v) = PE z :. v
  getIndex (EzVar k _ _) = k
  partialElems (EzVar _ ez v) = partialElems ez :. v
  partialIndex (z:.Var (!v)) !i !j = S.flatten mk step Unknown
                                   $ partialIndex z i j
    where mk   s = (s:.j-getIndex s)
          step (s:.z)
--            | z<0       = S.Done
--            | otherwise = let !k=j-z in S.Yield (EzVar k s (VU.unsafeIndex v k)) (s:.z-1) -- 'k'
            | z>=0      = let !k=j-z in S.Yield (EzVar k s (VU.unsafeIndex v k)) (s:.z-1)
            | otherwise = S.Done
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
  {-# INLINE partialElems #-}
  {-# INLINE getIndex #-}
  {-# INLINE partialIndex #-}



{-# NOINLINE complete3 #-}
complete3 :: Int -> Int -> Int
complete3 i j = S.foldl' min maxBound
              $ S.map (\(Z:.a:.b:.c) -> a+b+c)
              $ S.map completeElems
              $ completeIndex (Z:.Var v:.Var v:.Var v) i j

{-# NOINLINE complete5 #-}
complete5 :: Int -> Int -> Int
complete5 i j = S.foldl' min maxBound
              $ S.map (\(Z:.a:.b:.c:.d:.e) -> a+b+c+d+e)
              $ S.map completeElems
              $ completeIndex (Z:.Var v:.Var v:.Var v:.Var v:.Var v) i j

{-# NOINLINE abcdComp3 #-}
abcdComp3 :: Int -> Int -> ABCD
abcdComp3 i j = S.foldl' min D
              $ S.map (\(Z:.a:.b:.c) -> a `min` b `min` c)
              $ S.map completeElems
              $ completeIndex (Z:.Var w:.Var w:.Var w) i j

class CompleteIndex p where
  data F  p :: *
  type FE p :: *
  completeElems :: F p -> FE p
  fetIndex :: F p -> (Int:.Int)
  completeIndex :: p -> Int -> Int -> S.Stream (F p)

instance CompleteIndex Z where
  data F  Z = FZ !(Int:.Int)
  type FE Z = Z
  completeElems _ = Z
  fetIndex (FZ ix) = ix
  completeIndex _ i _ = S.singleton (FZ (i:.i))
  {-# INLINE completeElems #-}
  {-# INLINE fetIndex #-}
  {-# INLINE completeIndex #-}

instance (VU.Unbox v, CompleteIndex z) => CompleteIndex (z:.Var v) where
  data F  (z:.Var v) = FzVar !(Int:.Int) !(F z) !v
  type FE (z:.Var v) = FE z :. v
  fetIndex (FzVar ix _ _) = ix
  completeElems (FzVar _ fz v) = completeElems fz :. v
  completeIndex (z:.Var (!v)) !i !j = S.flatten mk step Unknown
                                    $ completeIndex z i j
    where mk   s = let (_:.l) = fetIndex s;z = j-l in (s:.l:.z)
          step (s:.k:.z)
            | z>=0      = let !l=j-z in S.Yield (FzVar (k:.l) s (VU.unsafeIndex v l)) (s:.k:.z-1)
            | otherwise = S.Done
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
  {-# INLINE completeElems #-}
  {-# INLINE fetIndex #-}
  {-# INLINE completeIndex #-}


main = defaultMain
  [ bgroup "partial"
--      [ bench " 1/ 10" $ whnf (partial  1)  10
--      , bench " 5/ 10" $ whnf (partial  5)  10
--      , bench " 1/100" $ whnf (partial  1) 100
      [ bench "50/ 100" $ whnf (partial3 50)  100
      , bench "50/ 100" $ whnf (partial5 50)  100
      , bench " 1/1000" $ whnf (partial3  1) 1000
      ]
  , bgroup "complete"
--      [ bench " 1/ 10" $ whnf (complete  1)  10
--      , bench " 5/ 10" $ whnf (complete  5)  10
--      , bench " 1/100" $ whnf (complete  1) 100
      [ bench "50/ 100" $ whnf (complete3 50)  100
      , bench "50/ 100" $ whnf (complete5 50)  100
      , bench " 1/1000" $ whnf (complete3  1) 1000
      ]
  , bgroup "abcd"
      [ bench "50/ 100" $ whnf (abcdComp3 50)  100
      , bench " 1/1000" $ whnf (abcdComp3  1) 1000
      ]
  ]

