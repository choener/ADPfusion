
module ADP.Fusion.Point.SynVar.Indices where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..),flatten)
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core
import ADP.Fusion.Core.SynVar.Indices
import ADP.Fusion.Point.Core



instance
  ( IndexHdr ps elm x0 i0 cs c us (PointL I) is (PointL I)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.IStatic d) elm (cs:.c) (us:.PointL I) (is:.PointL I) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') -> SvS s (t:.i) (y' :.: RiPlI (fromPointL i)))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}
{-
  addIndexDenseGo (cs:.c) (vs:.IVariable d) (ubs:..ub) (us:..u) (is:.PointL i)
    = flatten mk step . addIndexDenseGo cs vs ubs us is
    where mk svS = let RiPlI k = getIndex (getIdx $ sS svS {- sIx svS -} ) (Proxy :: PRI is (PointL I))
                   in  return $ svS :. k
          step (svS@(SvS s t y') :. k)
            | k + csize > i = return $ Done
            | otherwise     = return $ Yield (SvS s (t:.PointL k) (y' :.: RiPlI k)) (svS :. k+1)
            where csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}
-}

{-
instance
  ( IndexHdr s x0 i0 us (PointL O) cs c is (PointL O)
  ) => AddIndexDense s (us:.PointL O) (cs:.c) (is:.PointL O) where
  addIndexDenseGo (cs:._) (vs:.OStatic d) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') -> let RiPlO oi oo = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                            in  SvS s (t:.PointL oo) (y' :.: RiPlO oi oo) )
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (PointL I) cs c is (PointL C)
  ) => AddIndexDense s (us:.PointL I) (cs:.c) (is:.PointL C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y) -> let RiPlC k = getIndex (getIdx s) (Proxy :: PRI is (PointL C))
                           in  SvS s (t:.PointL k) (y :.: RiPlC k) )
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (PointL O) cs c is (PointL C)
  ) => AddIndexDense s (us:.PointL O) (cs:.c) (is:.PointL C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y) -> let RiPlC k = getIndex (getIdx s) (Proxy :: PRI is (PointL C))
                           in  SvS s (t:.PointL k) (y:.:RiPlC k) )
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}
-}

