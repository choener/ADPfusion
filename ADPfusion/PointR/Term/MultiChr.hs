
module ADPfusion.PointR.Term.MultiChr where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import           GHC.Exts
--import           GHC.TypeNats
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.MultiChr
import           ADPfusion.PointR.Core



type instance LeftPosTy (IStatic d)   (MultiChr c v x) (PointR I) = IStatic (d+c)
type instance LeftPosTy (IVariable d) (MultiChr c v x) (PointR I) = IVariable (d+c)



instance
  forall pos posLeft m ls c v x i
  . ( TermStream m (Z:.pos) (TermSymbol M (MultiChr c v x)) (Elm (Term1 (Elm ls (PointR i))) (Z :. PointR i)) (Z:.PointR i)
    , posLeft ~ LeftPosTy pos (MultiChr c v x) (PointR i)
    , TermStaticVar pos (MultiChr c v x) (PointR i)
    , MkStream m posLeft ls (PointR i)
    )
  ⇒ MkStream m pos (ls :!: MultiChr c v x) (PointR i) where
  mkStream pos (ls :!: MultiChr xs) grd us is
    = S.map (\(ss,ee,ii) -> ElmMultiChr ee ii ss) -- recover ElmChr
    . addTermStream1 pos (MultiChr @v @x @c xs) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos (MultiChr @v @x @c xs) us is grd) us (termStreamIndex pos (MultiChr @v @x @c xs) is)
  {-# Inline mkStream #-}


instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  , KnownNat c
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts (MultiChr c v x)) s (is:.PointR I) where
  termStream Proxy (ts:|MultiChr xs) (us:..LtPointR u) (is:.PointR i)
    = let !c = fromIntegral $ natVal (Proxy ∷ Proxy c) in
      S.map (\(TState s ii ee) ->
        let RiPrI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointR I))
        in  TState s (ii:.:RiPrI (k+c)) (ee:. VG.unsafeSlice k c xs))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointR I)
  , KnownNat c
  ) => TermStream m (ps:.IVariable d) (TermSymbol ts (MultiChr c v x)) s (is:.PointR I) where
  termStream Proxy (ts:|MultiChr xs) (us:..LtPointR u) (is:.PointR i)
    = let !c = fromIntegral $ natVal (Proxy ∷ Proxy c) in
      S.map (\(TState s ii ee) ->
        let RiPrI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointR I))
        in  TState s (ii:.:RiPrI (k+c)) (ee:. VG.unsafeSlice k c xs))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



instance (KnownNat c) ⇒ TermStaticVar (IStatic d) (MultiChr c v x) (PointR I) where
  termStreamIndex Proxy (MultiChr x) (PointR j) = PointR $ j
  termStaticCheck Proxy (MultiChr x) _ (PointR j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance (KnownNat c) ⇒ TermStaticVar (IVariable d) (MultiChr c v x) (PointR I) where
  termStreamIndex Proxy (MultiChr x) (PointR j) = PointR $ j
  termStaticCheck Proxy (MultiChr x) _ (PointR j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

