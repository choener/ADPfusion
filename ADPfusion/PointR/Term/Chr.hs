
module ADPfusion.PointR.Term.Chr where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Chr
import           ADPfusion.PointR.Core



type instance LeftPosTy (IStatic   d) (Chr r x) (PointR I) = IStatic   (d+1)
type instance LeftPosTy (IVariable d) (Chr r x) (PointR I) = IVariable (d+1)



instance
  forall pos posLeft m ls r x i
  . ( TermStream m (Z:.pos) (TermSymbol M (Chr r x)) (Elm (Term1 (Elm ls (PointR i))) (Z :. PointR i)) (Z:.PointR i)
    , posLeft ~ LeftPosTy pos (Chr r x) (PointR i)
    , TermStaticVar pos (Chr r x) (PointR i)
    , MkStream m posLeft ls (PointR i)
    )
  ⇒ MkStream m pos (ls :!: Chr r x) (PointR i) where
  {-# Inline mkStream #-}
  mkStream pos (ls :!: Chr f xs) grd us is
    = S.map (\(ss,ee,ii) -> ElmChr ee ii ss)
    . addTermStream1 pos (Chr f xs) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos (Chr f xs) us is grd) us (termStreamIndex pos (Chr f xs) is)


instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts (Chr r x)) s (is:.PointR I) where
  {-# Inline termStream #-}
  termStream Proxy (ts:|Chr f xs) (us:..LtPointR u) (is:.PointR i)
    = S.map (\(TState s ii ee) →
        let RiPrI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointR I))
        in  TState s (ii:.:RiPrI (k+1)) (ee:. f xs k))
    . termStream (Proxy ∷ Proxy ps) ts us is

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  ) => TermStream m (ps:.IVariable d) (TermSymbol ts (Chr r x)) s (is:.PointR I) where
  {-# Inline termStream #-}
  termStream Proxy (ts:|Chr f xs) (us:..LtPointR u) (is:.PointR i)
    = S.map (\(TState s ii ee) ->
        let RiPrI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointR I))
        in  TState s (ii:.:RiPrI (k+1)) (ee:. f xs k))
    . termStream (Proxy ∷ Proxy ps) ts us is



instance TermStaticVar (IStatic d) (Chr r x) (PointR I) where
  termStreamIndex Proxy (Chr f x) (PointR j) = PointR $ j
  termStaticCheck Proxy (Chr f x) (LtPointR _) (PointR j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (IVariable d) (Chr r x) (PointR I) where
  termStreamIndex Proxy (Chr f x) (PointR j) = PointR $ j
  termStaticCheck Proxy (Chr f x) (LtPointR _) (PointR j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

