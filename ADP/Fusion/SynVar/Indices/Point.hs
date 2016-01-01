
module ADP.Fusion.SynVar.Indices.Point where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( IndexHdr s x0 i0 us (PointL I) cs c is (PointL I)
  , MinSize c
  ) => AddIndexDense s (us:.PointL I) (cs:.c) (is:.PointL I) where
  addIndexDenseGo (cs:._) (vs:.IStatic d) (us:.u) (is:.i)
    = map (\(SvS s t y') -> SvS s (t:.i) (y' :.: RiPlI (fromPointL i)))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable d) (us:.u) (is:.PointL i)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = let RiPlI k = getIndex (getIdx $ sS svS {- sIx svS -} ) (Proxy :: PRI is (PointL I))
                   in  return $ svS :. k
          step (svS@(SvS s t y') :. k)
            | k + csize > i = return $ Done
            | otherwise     = return $ Yield (SvS s (t:.PointL k) (y' :.: RiPlI k)) (svS :. k+1)
            where csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (PointL O) cs c is (PointL O)
  ) => AddIndexDense s (us:.PointL O) (cs:.c) (is:.PointL O) where
  addIndexDenseGo (cs:._) (vs:.OStatic d) (us:.u) (is:.i)
    = map (\(SvS s t y') -> let RiPlO oi oo = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                            in  SvS s (t:.PointL oo) (y' :.: RiPlO oi oo) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (PointL I) cs c is (PointL C)
  ) => AddIndexDense s (us:.PointL I) (cs:.c) (is:.PointL C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s t y) -> let RiPlC k = getIndex (getIdx s) (Proxy :: PRI is (PointL C))
                           in  SvS s (t:.PointL k) (y :.: RiPlC k) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (PointL O) cs c is (PointL C)
  ) => AddIndexDense s (us:.PointL O) (cs:.c) (is:.PointL C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s t y) -> let RiPlC k = getIndex (getIdx s) (Proxy :: PRI is (PointL C))
                           in  SvS s (t:.PointL k) (y:.:RiPlC k) )
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

