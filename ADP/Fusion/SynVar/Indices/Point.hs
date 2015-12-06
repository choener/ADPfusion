
module ADP.Fusion.SynVar.Indices.Point where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( IndexHdr a us (PointL I) is (PointL I)
  ) => AddIndexDense a (us:.PointL I) (is:.PointL I) where
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
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          csize = delay_inline minSize c
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (PointL O) is (PointL O)
  ) => AddIndexDense a (us:.PointL O) (is:.PointL O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic d) (us:.u) (is:.i)
    = map (\(SvS s a t y') -> let RiPlO oi oo = getIndex a (Proxy :: PRI is (PointL O))
                              in  SvS s a (t:.PointL oo) (y' :.: RiPlO oi oo) )
    . addIndexDenseGo cs vs us is
    where csize = delay_inline minSize c
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (PointL I) is (PointL C)
  ) => AddIndexDense a (us:.PointL I) (is:.PointL C) where
  addIndexDenseGo (cs:.c) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y) -> let RiPlC k _ = getIndex a (Proxy :: PRI is (PointL C))
                             in  SvS s a (t:.PointL k) (y :.: RiPlC k k) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (PointL O) is (PointL C)
  ) => AddIndexDense a (us:.PointL O) (is:.PointL C) where
  addIndexDenseGo (cs:.c) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y) -> let RiPlC k _ = getIndex a (Proxy :: PRI is (PointL C))
                             in  SvS s a (t:.PointL k) (y:.:RiPlC k k) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

