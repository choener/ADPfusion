
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

-- * With 'tableIndices' we create a stream of legal indices for this table. We
-- need 'tableIndices' in multi-dimensional tables as the type of the
-- multi-dimensional indices is generic.

module ADP.Fusion.Table.Indices where

import           Data.Vector.Fusion.Stream.Size (Size(Unknown))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray -- (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR)

import           ADP.Fusion.Classes
import           ADP.Fusion.Multi.Classes



class TableIndices i where
  tableIndices :: (Monad m) => TblConstraint i -> IxSV i -> i -> S.Stream m (Triple z j i) -> S.Stream m (Triple z j i)

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
  tableIndices (cs:.c) (vs:.Static) (is:.PointL (i:.j))
    = id -- staticCheck (i<=j)
    . S.map (\(Tr s (x:.PointL (_:.l)) ys) -> Tr s x (is:.pointL l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.PointL (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.PointL (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.pointL k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}

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

