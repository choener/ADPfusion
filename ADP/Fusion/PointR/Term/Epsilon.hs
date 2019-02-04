
-- | Rules of the type @X → ε@ denote termination of parsing if @X@ is empty.

module ADP.Fusion.PointR.Term.Epsilon where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Core.Term.Epsilon
import           ADP.Fusion.PointR.Core



type instance LeftPosTy (IStatic d) Epsilon (PointR I) = IStatic d

instance
  forall pos posLeft m ls i
  . ( TermStream m (Z:.pos) (TermSymbol M Epsilon) (Elm (Term1 (Elm ls (PointR i))) (Z :. PointR i)) (Z:.PointR i)
    , posLeft ~ LeftPosTy pos Epsilon (PointR i)
    , TermStaticVar pos Epsilon (PointR i)
    , MkStream m posLeft ls (PointR i)
    )
  ⇒ MkStream m pos (ls :!: Epsilon) (PointR i) where
  mkStream Proxy (ls :!: Epsilon) grd us is
    = S.map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 (Proxy ∷ Proxy pos) Epsilon us is
    $ mkStream (Proxy ∷ Proxy posLeft)
               ls
               (termStaticCheck (Proxy ∷ Proxy pos) Epsilon us is grd)
               us
               (termStreamIndex (Proxy ∷ Proxy pos) Epsilon is)
  {-# Inline mkStream #-}


instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  )
  ⇒ TermStream m (ps:.IStatic d) (TermSymbol ts Epsilon) s (is:.PointR I) where
  termStream Proxy (ts:|Epsilon) (us:..LtPointR u) (is:.PointR i)
    = S.map (\(TState s ii ee) ->
              let RiPrI k = getIndex (getIdx s) (Proxy :: PRI is (PointR I))
              in  TState s (ii:.:RiPrI k) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



-- TODO need upper bound in @termStaticCheck@ to be able to check against that!

instance TermStaticVar (IStatic 0) Epsilon (PointR I) where
  termStreamIndex Proxy Epsilon (PointR i     ) = PointR i
  termStaticCheck Proxy Epsilon (LtPointR (I# u)) (PointR (I# i)) grd = (i ==# u) `andI#` grd
  {-# Inline termStreamIndex #-}
  {-# Inline termStaticCheck #-}

