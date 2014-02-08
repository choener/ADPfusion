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
import           Data.Array.Repa.Index
import           Data.Array.Repa.Shape
import           Criterion.Main

{-# NOINLINE v #-}
v :: VU.Vector Int
v = VU.fromList [1..1000]

data Var x = Var (VU.Vector x)
  deriving (Show)


{-# NOINLINE partial #-}
partial :: Int -> Int -> Int
partial i j = S.foldl' (+) 0
            $ S.map (\(Z:.a:.b:.c) -> a+b+c)
            $ S.map partialElems
            $ partialIndex (Z:.Var v:.Var v:.Var v) i j

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
    where mk   s = (s:.getIndex s)
          step (s:.k)
            | k>j       = S.Done
            | otherwise = S.Yield (EzVar k s (VU.unsafeIndex v k)) (s:.k+1)
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
  {-# INLINE partialElems #-}
  {-# INLINE getIndex #-}
  {-# INLINE partialIndex #-}



{-# NOINLINE complete #-}
complete :: Int -> Int -> Int
complete i j = S.foldl' (+) 0
             $ S.map (\(Z:.a:.b:.c) -> a+b+c)
             $ S.map completeElems
             $ completeIndex (Z:.Var v:.Var v:.Var v) i j

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
    where mk   s = let (k:.l) = fetIndex s in (s:.(l:.l))
          step (s:.(k:.l))
            | l>j       = S.Done
            | otherwise = S.Yield (FzVar (k:.l) s (VU.unsafeIndex v l)) (s:.(k:.l+1))
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
      [ bench "50/100" $ whnf (partial 50) 100
      ]
  , bgroup "complete"
--      [ bench " 1/ 10" $ whnf (complete  1)  10
--      , bench " 5/ 10" $ whnf (complete  5)  10
--      , bench " 1/100" $ whnf (complete  1) 100
      [ bench "50/100" $ whnf (complete 50) 100
      ]
  ]

