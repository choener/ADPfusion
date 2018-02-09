
module ADP.Fusion.Point.Term.Deletion where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Core.Term.Deletion
import           ADP.Fusion.Point.Core



type instance LeftPosTy (IStatic d) Deletion (PointL I) = IStatic d

type instance LeftPosTy (OStatic d) Deletion (PointL O) = OStatic d

instance
  forall pos posLeft m ls i
  . ( TermStream m (Z:.pos) (TermSymbol M Deletion) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos Deletion (PointL i)
    , TermStaticVar pos Deletion (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  ⇒ MkStream m pos (ls :!: Deletion) (PointL i) where
  mkStream pos (ls :!: Deletion) grd us is
    = S.map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 pos Deletion us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (grd `andI#` termStaticCheck pos Deletion is) us (termStreamIndex pos Deletion is)
  {-# Inline mkStream #-}



instance
  ( TstCtx m ps ts s x0 i0 is (PointL I)
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts Deletion) s (is:.PointL I) where
  termStream Proxy (ts:|Deletion) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TstCtx m ps ts s x0 i0 is (PointL O)
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts Deletion) s (is:.PointL O) where
  termStream Proxy (ts:|Deletion) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let io = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.: io) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



instance TermStaticVar (IStatic d) Deletion (PointL I) where
  termStreamIndex Proxy Deletion (PointL j) = PointL j
  termStaticCheck Proxy Deletion (PointL j) = 1#
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar oAny Deletion (PointL O) where
  termStreamIndex Proxy Deletion (PointL j) = PointL j
  termStaticCheck Proxy Deletion (PointL j) = 1#
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

