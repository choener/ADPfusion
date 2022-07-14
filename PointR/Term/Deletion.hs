
module ADPfusion.PointR.Term.Deletion where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Deletion
import           ADPfusion.PointR.Core



type instance LeftPosTy (IStatic   d) Deletion (PointR I) = IStatic d
type instance LeftPosTy (IVariable d) Deletion (PointR I) = IVariable d



instance
  forall pos posLeft m ls i
  . ( TermStream m (Z:.pos) (TermSymbol M Deletion) (Elm (Term1 (Elm ls (PointR i))) (Z :. PointR i)) (Z:.PointR i)
    , posLeft ~ LeftPosTy pos Deletion (PointR i)
    , TermStaticVar pos Deletion (PointR i)
    , MkStream m posLeft ls (PointR i)
    )
  ⇒ MkStream m pos (ls :!: Deletion) (PointR i) where
  {-# Inline mkStream #-}
  mkStream pos (ls :!: Deletion) grd us is
    = S.map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 pos Deletion us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos Deletion us is grd) us (termStreamIndex pos Deletion is)



instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts Deletion) s (is:.PointR I) where
  {-# Inline termStream #-}
  termStream Proxy (ts:|Deletion) (us:..LtPointR u) (is:.PointR i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPrI i) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  )
  ⇒ TermStream m (ps:.IVariable d) (TermSymbol ts Deletion) s (is:.PointR I) where
  {-# Inline termStream #-}
  termStream Proxy (ts:|Deletion) (us:..LtPointR u) (is:.PointR i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPrI i) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is



instance TermStaticVar (IStatic d) Deletion (PointR I) where
  termStreamIndex Proxy Deletion (PointR j) = PointR j
  termStaticCheck Proxy Deletion _ (PointR j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (IVariable d) Deletion (PointR I) where
  termStreamIndex Proxy Deletion (PointR j) = PointR j
  termStaticCheck Proxy Deletion _ (PointR j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

