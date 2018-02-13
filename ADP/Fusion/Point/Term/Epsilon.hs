
-- | Rules of the type @X → ε@ denote termination of parsing if @X@ is empty.

module ADP.Fusion.Point.Term.Epsilon where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Core.Term.Epsilon
import           ADP.Fusion.Point.Core



type instance LeftPosTy (IStatic d) Epsilon (PointL I) = IStatic d
--type instance LeftPosTy (IVariable d) Epsilon (PointL I) = IVariable d

type instance LeftPosTy (OStatic d) Epsilon (PointL O) = OStatic d

instance
  forall pos posLeft m ls i
  . ( TermStream m (Z:.pos) (TermSymbol M Epsilon) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos Epsilon (PointL i)
    , TermStaticVar pos Epsilon (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  ⇒ MkStream m pos (ls :!: Epsilon) (PointL i) where
  mkStream Proxy (ls :!: Epsilon) grd us is
    = S.map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 (Proxy ∷ Proxy pos) Epsilon us is
    $ mkStream (Proxy ∷ Proxy posLeft)
               ls
               (grd `andI#` termStaticCheck (Proxy ∷ Proxy pos) Epsilon is)
               us
               (termStreamIndex (Proxy ∷ Proxy pos) Epsilon is)
  {-# Inline mkStream #-}


instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts Epsilon) s (is:.PointL I) where
  termStream Proxy (ts:|Epsilon) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
              let RiPlI k = getIndex (getIdx s) (Proxy :: PRI is (PointL I))
              in  TState s (ii:.:RiPlI k) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

{-
instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  )
  ⇒ TermStream m (ps:.IVariable d) (TermSymbol ts Epsilon) s (is:.PointL I) where
  termStream Proxy (ts:|Epsilon) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
              let RiPlI k = getIndex (getIdx s) (Proxy :: PRI is (PointL I))
              in  TState s (ii:.:RiPlI k) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}
-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O)
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts Epsilon) s (is:.PointL O) where
  termStream Proxy (ts:|Epsilon) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let io = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.:io) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

-- | We assume that @ε / Epsilon@ is ever only the single symbol (maybe apart
-- from @- / Deletion@) on a tape. Hence The instance is only active in
-- @IStatic 0@ cases.

instance TermStaticVar (IStatic 0) Epsilon (PointL I) where
  termStreamIndex Proxy Epsilon (PointL i     ) = PointL i
  termStaticCheck Proxy Epsilon (PointL (I# i)) = i ==# 0#
  {-# Inline termStreamIndex #-}
  {-# Inline termStaticCheck #-}

instance TermStaticVar (OStatic 0) Epsilon (PointL O) where
  termStreamIndex Proxy Epsilon (PointL i     ) = PointL i
  termStaticCheck Proxy Epsilon (PointL (I# i)) = 1#
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

