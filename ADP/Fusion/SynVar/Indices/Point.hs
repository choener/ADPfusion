
module ADP.Fusion.SynVar.Indices.Point where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( AddIndexDense a is
  , GetIndex a is
  , GetIx a (is:.PointL) ~ PointL
  ) => AddIndexDense a (is:.PointL) where
  addIndexDenseGo (cs:._) (vs:.IStatic d) (us:.u) (is:.i)
    = map (\(S5 s a b y z) -> S5 s a b (y:.i) (z:.PointL 0))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable d) (us:.u) (is:.PointL i)
    = flatten mk step Unknown . addIndexDenseGo cs vs us is
    where mk (S5 s a b y z) = let PointL k = getIndex a (Proxy :: Proxy (is:.PointL))
                              in  return $ S6 s a b y z k
          step (S6 s a b y z k)
            | k + csize > i = return $ Done
            | otherwise     = return $ Yield (S5 s a b (y:.PointL k) (z:.PointL 0)) (S6 s a b y z (k+1))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          csize = delay_inline minSize c
  {-# Inline addIndexDenseGo #-}

