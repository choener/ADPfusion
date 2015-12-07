
module ADP.Fusion.SynVar.Indices.Point where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( IndexHdr a us (PointL I) cs c is (PointL I)
  , MinSize c
  ) => AddIndexDense a (us:.PointL I) (cs:.c) (is:.PointL I) where
  addIndexDenseGo (cs:._) (vs:.IStatic d) (us:.u) (is:.i)
    = map (\(SvS s a t y') -> SvS s a (t:.i) (y' :.: RiPlI (fromPointL i)))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable d) (us:.u) (is:.PointL i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = let RiPlI k = getIndex (sIx svS) (Proxy :: PRI is (PointL I))
                   in  return $ svS :. k
          step (svS@(SvS s a t y') :. k)
            | k + csize > i = return $ Done
            | otherwise     = return $ Yield (SvS s a (t:.PointL k) (y' :.: RiPlI k)) (svS :. k+1)
            where csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (PointL O) cs c is (PointL O)
  ) => AddIndexDense a (us:.PointL O) (cs:.c) (is:.PointL O) where
  addIndexDenseGo (cs:._) (vs:.OStatic d) (us:.u) (is:.i)
    = map (\(SvS s a t y') -> let RiPlO oi oo = getIndex a (Proxy :: PRI is (PointL O))
                              in  SvS s a (t:.PointL oo) (y' :.: RiPlO oi oo) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (PointL I) cs c is (PointL C)
  ) => AddIndexDense a (us:.PointL I) (cs:.c) (is:.PointL C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y) -> let RiPlC k _ = getIndex a (Proxy :: PRI is (PointL C))
                             in  SvS s a (t:.PointL k) (y :.: RiPlC k k) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (PointL O) cs c is (PointL C)
  ) => AddIndexDense a (us:.PointL O) (cs:.c) (is:.PointL C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y) -> let RiPlC k _ = getIndex a (Proxy :: PRI is (PointL C))
                             in  SvS s a (t:.PointL k) (y:.:RiPlC k k) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

