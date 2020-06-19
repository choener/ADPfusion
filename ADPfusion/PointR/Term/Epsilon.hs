
-- | Rules of the type @X → ε@ denote termination of parsing if @X@ is empty.

module ADPfusion.PointR.Term.Epsilon where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Epsilon
import           ADPfusion.PointR.Core



type instance LeftPosTy (IStatic d) (Epsilon Global) (PointR I) = IStatic d

instance
  forall pos posLeft m ls i lg
  . ( TermStream m (Z:.pos) (TermSymbol M (Epsilon lg)) (Elm (Term1 (Elm ls (PointR i))) (Z :. PointR i)) (Z:.PointR i)
    , posLeft ~ LeftPosTy pos (Epsilon lg) (PointR i)
    , TermStaticVar pos (Epsilon lg) (PointR i)
    , MkStream m posLeft ls (PointR i)
    )
  ⇒ MkStream m pos (ls :!: Epsilon lg) (PointR i) where
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
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts (Epsilon lg)) s (is:.PointR I) where
  termStream Proxy (ts:|Epsilon) (us:..LtPointR u) (is:.PointR i)
    = S.map (\(TState s ii ee) ->
              let RiPrI k = getIndex (getIdx s) (Proxy :: PRI is (PointR I))
              in  TState s (ii:.:RiPrI k) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



-- TODO need upper bound in @termStaticCheck@ to be able to check against that!

instance TermStaticVar (IStatic 0) (Epsilon Global) (PointR I) where
  termStreamIndex Proxy Epsilon (PointR i     ) = PointR i
  termStaticCheck Proxy Epsilon (LtPointR (I# u)) (PointR (I# i)) grd = (i ==# u) `andI#` grd
  {-# Inline termStreamIndex #-}
  {-# Inline termStaticCheck #-}

instance TermStaticVar (IStatic 0) (Epsilon Local) (PointR I) where
  termStreamIndex Proxy Epsilon (PointR i     ) = PointR i
  termStaticCheck Proxy Epsilon (LtPointR (I# u)) (PointR (I# i)) grd = grd
  {-# Inline termStreamIndex #-}
  {-# Inline termStaticCheck #-}

