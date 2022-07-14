
module ADPfusion.PointL.Term.PeekIndex where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.PeekIndex
import           ADPfusion.PointL.Core



type instance LeftPosTy (IStatic   d) (PeekIndex pi) (PointL I) = IStatic d
type instance LeftPosTy (IVariable d) (PeekIndex pi) (PointL I) = IVariable d

type instance LeftPosTy (OStatic d) (PeekIndex pi) (PointL O) = OStatic d

instance
  forall pos posLeft m ls i pi
  . ( TermStream m (Z:.pos) (TermSymbol M (PeekIndex pi)) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos (PeekIndex pi) (PointL i)
    , TermStaticVar pos (PeekIndex pi) (PointL i)
    , MkStream m posLeft ls (PointL i)
    , pi ~ PointL i
    )
  ⇒ MkStream m pos (ls :!: PeekIndex pi) (PointL i) where
  mkStream pos (ls :!: PeekIndex) grd us is
    = S.map (\(ss,ee,ii) -> ElmPeekIndex is ii ss)
    . addTermStream1 pos (PeekIndex @pi) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos (PeekIndex @pi) us is grd) us (termStreamIndex pos (PeekIndex @pi) is)
  {-# Inline mkStream #-}



instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  , pi ~ PointL I
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts (PeekIndex pi)) s (is:.PointL I) where
  termStream Proxy (ts:|PeekIndex) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:.pointLI i))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  , pi ~ PointL I
  )
  ⇒ TermStream m (ps:.IVariable d) (TermSymbol ts (PeekIndex pi)) s (is:.PointL I) where
  termStream Proxy (ts:|PeekIndex) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:.pointLI i))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O)
  , pi ~ PointL O
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts (PeekIndex pi)) s (is:.PointL O) where
  termStream Proxy (ts:|PeekIndex) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let io = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.: io) (ee:.pointLO i))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



instance TermStaticVar (IStatic d) (PeekIndex i) (PointL I) where
  termStreamIndex Proxy PeekIndex (PointL j) = PointL j
  termStaticCheck Proxy PeekIndex _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (IVariable d) (PeekIndex i) (PointL I) where
  termStreamIndex Proxy PeekIndex (PointL j) = PointL j
  termStaticCheck Proxy PeekIndex _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar oAny (PeekIndex o) (PointL O) where
  termStreamIndex Proxy PeekIndex (PointL j) = PointL j
  termStaticCheck Proxy PeekIndex _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

