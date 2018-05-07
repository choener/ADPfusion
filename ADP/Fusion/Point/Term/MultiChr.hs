
module ADP.Fusion.Point.Term.MultiChr where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import           GHC.Exts
--import           GHC.TypeNats
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Core.Term.MultiChr
import           ADP.Fusion.Point.Core



type instance LeftPosTy (IStatic d) (MultiChr c v x) (PointL I) = IStatic d
--type instance LeftPosTy (IVariable d) (Chr r x) (PointL I) = IVariable d

type instance LeftPosTy (OStatic d) (MultiChr c v x) (PointL O) = OStatic (d + c)

-- | First try in getting this right with a @termStream@.
--
-- TODO use @PointL i@ since this is probably the same for all single-tape
-- instances with @ElmChr@.
--
-- TODO it might even be possible to auto-generate this code via TH.

instance
  forall pos posLeft m ls c v x i
  . ( TermStream m (Z:.pos) (TermSymbol M (MultiChr c v x)) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos (MultiChr c v x) (PointL i)
    , TermStaticVar pos (MultiChr c v x) (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  ⇒ MkStream m pos (ls :!: MultiChr c v x) (PointL i) where
  mkStream pos (ls :!: MultiChr xs) grd us is
    = S.map (\(ss,ee,ii) -> ElmMultiChr ee ii ss) -- recover ElmChr
    . addTermStream1 pos (MultiChr @c xs) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos (MultiChr @c xs) is grd) us (termStreamIndex pos (MultiChr @c xs) is)
  {-# Inline mkStream #-}


-- | 

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  , KnownNat c
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts (MultiChr c v x)) s (is:.PointL I) where
  termStream Proxy (ts:|MultiChr xs) (us:..LtPointL u) (is:.PointL i)
    = let c = fromIntegral $ natVal (Proxy ∷ Proxy c) in
      S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:. VG.unsafeSlice (i-c) c xs))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O)
  , KnownNat c
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts (MultiChr c v x)) s (is:.PointL O) where
  termStream Proxy (ts:|MultiChr xs) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlO k o = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                    c = fromIntegral $ natVal (Proxy ∷ Proxy c)
                in  TState s (ii:.: RiPlO (k+c) o) (ee:.VG.unsafeSlice k c xs))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



instance (KnownNat c) ⇒ TermStaticVar (IStatic d) (MultiChr c v x) (PointL I) where
  termStreamIndex Proxy (MultiChr x) (PointL j) = PointL $ j-(fromIntegral $ natVal (Proxy ∷ Proxy c))
  termStaticCheck Proxy (MultiChr x) (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (OStatic d) (MultiChr c v x) (PointL O) where
  termStreamIndex Proxy (MultiChr x) (PointL j) = PointL $ j
  -- | TODO check if @c@ to the right goes out of bounds?
  termStaticCheck Proxy (MultiChr x) (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

