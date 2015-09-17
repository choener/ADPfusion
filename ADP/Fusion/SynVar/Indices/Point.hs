
module ADP.Fusion.SynVar.Indices.Point where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( AddIndexDense a us is
  , GetIndex a (is:.PointL I)
  , GetIx a (is:.PointL I) ~ (PointL I)
  ) => AddIndexDense a (us:.PointL I) (is:.PointL I) where
  addIndexDenseGo (cs:._) (vs:.IStatic d) (us:.u) (is:.i)
    = map (\(S7 s a b y z y' z') -> S7 s a b (y:.i) (z:.PointL 0) (y':.i) (z':.PointL 0))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable d) (us:.u) (is:.PointL i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk (S7 s a b y z y' z') = let PointL k = getIndex a (Proxy :: Proxy (is:.PointL I))
                                    in  return $ S8 s a b y z y' z' k
          step (S8 s a b y z y' z' k)
            | k + csize > i = return $ Done
            | otherwise     = return $ Yield (S7 s a b (y:.PointL k) (z:.PointL 0) (y':.PointL k) (z':.PointL 0)) (S8 s a b y z y' z' (k+1))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          csize = delay_inline minSize c
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.PointL O)
  , GetIx a (is:.PointL O) ~ (PointL O)
  ) => AddIndexDense a (us:.PointL O) (is:.PointL O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic d) (us:.u) (is:.i)
    = map (\(S7 s a b y z y' z') -> let o = getIndex b (Proxy :: Proxy (is:.PointL O))
                                    in  S7 s a b (y:.o) (z:.o) (y':.o) (z':.o))
    . addIndexDenseGo cs vs us is
    where csize = delay_inline minSize c
  {-# Inline addIndexDenseGo #-}

