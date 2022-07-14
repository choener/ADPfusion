
-- | Rules of the type @X → ε@ denote termination of parsing if @X@ is empty.

module ADPfusion.PointL.Term.Epsilon where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Epsilon
import           ADPfusion.PointL.Core



type instance LeftPosTy (IStatic d) (Epsilon Global) (PointL I) = IStatic d
type instance LeftPosTy (IStatic d) (Epsilon Local) (PointL I) = IVariable d  -- to actually allow local epsilons to work, IStatic does additional static controls
--type instance LeftPosTy (IVariable d) Epsilon (PointL I) = IVariable d

type instance LeftPosTy (OStatic d) (Epsilon Global) (PointL O) = OStatic d

instance
  forall pos posLeft m ls i lg
  . ( TermStream m (Z:.pos) (TermSymbol M (Epsilon lg)) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos (Epsilon lg) (PointL i)
    , TermStaticVar pos (Epsilon lg) (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  ⇒ MkStream m pos (ls :!: (Epsilon lg)) (PointL i) where
  mkStream Proxy (ls :!: Epsilon) grd us is
    = S.map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 (Proxy ∷ Proxy pos) (Epsilon @lg) us is
    $ mkStream (Proxy ∷ Proxy posLeft)
               ls
               (termStaticCheck (Proxy ∷ Proxy pos) (Epsilon @lg) us is grd)
               us
               (termStreamIndex (Proxy ∷ Proxy pos) (Epsilon @lg) is)
  {-# Inline mkStream #-}


instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts (Epsilon lg)) s (is:.PointL I) where
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
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts (Epsilon lg)) s (is:.PointL O) where
  termStream Proxy (ts:|Epsilon) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let io = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.:io) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

-- | We assume that @ε / Epsilon@ is ever only the single symbol (maybe apart
-- from @- / Deletion@) on a tape. Hence The instance is only active in
-- @IStatic 0@ cases.

instance TermStaticVar (IStatic 0) (Epsilon Global) (PointL I) where
  termStreamIndex Proxy Epsilon (PointL i     ) = PointL i
  termStaticCheck Proxy Epsilon _ (PointL (I# i)) grd = (i ==# 0#) `andI#` grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (IStatic 0) (Epsilon Local) (PointL I) where
  termStreamIndex Proxy Epsilon (PointL i     ) = PointL i
  -- | Local epsilons are *always* possible.
  termStaticCheck Proxy Epsilon _ (PointL (I# i)) grd = grd
  {-# Inline termStreamIndex #-}
  {-# Inline termStaticCheck #-}

instance TermStaticVar (OStatic 0) (Epsilon Global) (PointL O) where
  termStreamIndex Proxy Epsilon (PointL i     ) = PointL i
  -- |
  --
  -- TODO Consider this as a potential bug: we do *not* check that the upper
  -- bound @us@ (which we not even hand over to termStaticCheck but should) is
  -- equal to the current index @i@. HERE this ends up not being a bug because
  -- @Epsilon@ keeps the positional system at @OStatic@ and does not move to
  -- @ORightOf@ or anything, and in correct epsilon rules, everything is fine.
  --
  -- We even end up being correct with @X -> whatever epsilon@ because epsilon
  -- is neutral ...
  --
  -- TODO But we should probably statically assert that epsilon is the only
  -- symbol on the r.h.s. of whatever we write ...
  termStaticCheck Proxy Epsilon (LtPointL (I# u)) (PointL (I# i)) grd = (u ==# i) `andI#` grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (OStatic 0) (Epsilon Local) (PointL O) where
  termStreamIndex Proxy Epsilon (PointL i     ) = PointL i
  termStaticCheck Proxy Epsilon (LtPointL (I# u)) (PointL (I# i)) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

