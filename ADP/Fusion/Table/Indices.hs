
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

-- * With 'tableIndices' we create a stream of legal indices for this table. We
-- need 'tableIndices' in multi-dimensional tables as the type of the
-- multi-dimensional indices is generic.

module ADP.Fusion.Table.Indices where

import Data.Vector.Fusion.Stream.Size (Size(Unknown))
import Data.Vector.Fusion.Stream.Monadic (flatten,map,Stream, Step(..))
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base



class TableIndices i where
  tableIndices :: (Monad m) => TblConstraint i -> Context i -> i -> Stream m (S5 z j j i i) -> Stream m (S5 z j j i i)

instance TableIndices Z where
  tableIndices _ _ _ = id
  {-# INLINE tableIndices #-}

{-
instance TableIndices is => TableIndices (is:.Subword) where
  tableIndices (cs:.c) (vs:.Static) (is:.Subword (i:.j))
    = S.map (\(Tr s (x:.Subword (_:.l)) ys) -> Tr s x (is:.subword l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.Subword (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.Subword (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.subword k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}
-}

instance TableIndices is => TableIndices (is:.PointL) where
  tableIndices (cs:.c) (vs:.IStatic) (is:.PointL j)
    = map (\(S5 s (zi:.PointL _) (zo:.PointL _) is os) -> S5 s zi zo (is:.PointL j) (os:.PointL 0)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.IVariable) (is:.PointL j)
    = flatten mk step Unknown
    . tableIndices cs vs is
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    where mk (S5 s (zi:.PointL l) (zo:._) is os) = return $ S6 s zi zo is os (j-l-minSize c)
          step (S6 s zi zo is os x)
            | x >= 0    = return $ Yield (S5 s zi zo (is:.PointL (j-x)) (os:.PointL 0)) (S6 s zi zo is os (x-1))
            | otherwise = return $ Done
          {-# Inline [1] mk   #-}
          {-# Inline [1] step #-}
    {-
    where mk (S5 s (y:.PointL (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.pointL k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
            -}
  {-# Inline tableIndices #-}

{-
instance TableIndices is => TableIndices (is:.PointR) where
  tableIndices (cs:.c) (vs:.Static) (is:.PointR (i:.j))
    = S.map (\(Tr s (x:.PointR (_:.l)) ys) -> Tr s x (is:.pointR l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.PointR (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.PointR (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.pointR k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}
-}

