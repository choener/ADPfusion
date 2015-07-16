
-- | With 'tableIndices' we create a stream of legal indices for this table. We
-- need 'tableIndices' in multi-dimensional tables as the type of the
-- multi-dimensional indices is generic.

module ADP.Fusion.SynVar.Indices where

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

instance TableIndices (Outside Z) where
  tableIndices _ _ _ = id
  {-# INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.Subword) where
  tableIndices (cs:._) (vs:.IStatic _) (ixs:.Subword (i:.j))
    = map (\(S5 s (zi:.Subword (_:.l)) (zo:._) is os) -> S5 s zi zo (is:.subword l j) (os:.subword 0 0))
    . tableIndices cs vs ixs
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
  -- TODO ? using the defns in TermSymbol.hs for Array syns?
  {-
  tableIndices (cs:._) (vs:.IVariable _) (ixs:.Subword (i:.j))
    = map (\(S5 s (zi:.Subword (_:.l)) (zo:._) is os) -> S5 s zi zo (is:.subword l j) (os:.subword 0 0))
    . tableIndices cs vs ixs
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
  -}
  -- TODO minsize handling ? constraint handling?
  tableIndices (cs:._) (vs:.IVariable _) (ixs:.Subword (i:.j))
    = flatten mk step Unknown
    . tableIndices cs vs ixs
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    where mk (S5 s (zi:.Subword (_:.l)) (zo:._) is os) = return (S5 s zi zo is os :. l :. j - l)
          step (s5:.k:.z) | z >= 0 = do let S5 s zi zo is os = s5
                                            l                = j - z
                                            kl               = subword k l
                                        return $ Yield (S5 s zi zo (is:.kl) (os:.subword 0 0)) (s5 :. k :. z-1)
                          | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline tableIndices #-}

{-
    where mk (S6 s (zi:.(Subword (_:.l))) (zo:._) is os e) = return (S6 s zi zo is os e :. l :. j - l) -- TODO minsize c !
          step (s6:.k:.z) | z >= 0 = do let S6 s zi zo is os e = s6
                                            l                  = j - z
                                            kl                 = subword k l
                                        return $ Yield (S6 s zi zo (is:.kl) (os:.subword 0 0) (e:.(t!kl))) (s6 :. k :. z-1)
                          | otherwise = return $ Done
-}

{-
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

-- | TODO I think we need to check @cs:.c@ here
--
-- TODO yes, handle @Empty@ / @NonEmpty@ !!!

instance TableIndices is => TableIndices (is:.PointL) where
  tableIndices (cs:._) (vs:.IStatic _) (is:.PointL j)
    = map (\(S5 s (zi:.PointL _) (zo:.PointL _) is os) -> S5 s zi zo (is:.PointL j) (os:.PointL 0)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
  tableIndices (cs:._) (vs:.IVariable d) (is:.PointL j)
    = flatten mk step Unknown
    . tableIndices cs vs is
    . map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    where mk s@(S5 _ (_:.PointL k) _ _ _) = return (s :. k)
          step (ss@(S5 s (zi:._) (zo:._) is os) :. k)
            | k > j     = return $ Done
            | otherwise = return $ Yield (S5 s zi zo (is:.PointL k) (os:.PointL 0)) (ss :. k+1)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-  TODO re-add later
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
  -}
  {-# Inline tableIndices #-}

instance TableIndices (Outside is) => TableIndices (Outside (is:.PointL)) where
  tableIndices (cs:.c) (vs:.OStatic d) (O (is:.PointL j))
    = map (\(S5 s (zi:.PointL i) (zo:.PointL o) (O is) (O os)) -> S5 s zi zo (O (is:.PointL i)) (O (os:.PointL o))) -- constraint handled: tableStreamIndex
    . tableIndices cs vs (O is)
    . map (\(S5 s zi zo (O (is:.i)) (O (os:.o))) -> S5 s (zi:.i) (zo:.o) (O is) (O os))
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

