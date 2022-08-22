
module ADPfusion.PointL.Term.Str where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import           GHC.Exts
import           Data.Type.Equality
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           Text.Printf

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Str
import           ADPfusion.PointL.Core



-- * Inside

type instance LeftPosTy (IStatic   '(low,high)) (Str linked minSz maxSz v x r) (PointL I) = IVariable '(low+minSz,high+maxSz)
type instance LeftPosTy (IVariable '(low,high)) (Str linked minSz maxSz v x r) (PointL I) = IVariable '(low+minSz,high+maxSz)

-- | 

instance
  forall pos posLeft m ls linked minSz maxSz v x r i
  . ( TermStream m (Z:.pos) (TermSymbol M (Str linked minSz maxSz v x r))
                 (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos (Str linked minSz maxSz v x r) (PointL i)
    , TermStaticVar pos (Str linked minSz maxSz v x r) (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  => MkStream m pos (ls :!: Str linked minSz maxSz v x r) (PointL i) where
--{{{
  {-# Inline mkStream #-}
  mkStream pos (ls :!: Str f xs) grd us is
    = S.map (\(ss,ee,ii) -> ElmStr ee ii ss) -- recover ElmChr
    . addTermStream1 pos (Str @v @x @r @linked @minSz @maxSz f xs) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls
               (termStaticCheck pos (Str @v @x @r @linked @minSz @maxSz f xs) us is grd)
               us (termStreamIndex pos (Str @v @x @r @linked @minSz @maxSz f xs) is)
--}}}

-- | Note that the @minSz@ should automatically work out due to the encoding in
-- @d@.
--
-- TODO handle minSz/maxSz

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I), KnownNat low, KnownNat high) =>
  TermStream m (ps:.IStatic '(low,high)) (TermSymbol ts (Str linked minSz maxSz v x r)) s (is:.PointL I) where
--{{{
  {-# Inline termStream #-}
  termStream Proxy (ts:|Str f xs) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointL I))
                in  TState s (ii:.:RiPlI i) (ee:.f xs k (i-low)))
    . termStream (Proxy ∷ Proxy ps) ts us is
    where !low = fromIntegral $ natVal (Proxy @low)
--}}}



-- * Outside

type instance LeftPosTy (OStatic '(low,high)) (Str linked minSz maxSz v x r) (PointL O) = ORightOf '(low+minSz,high+maxSz)
type instance LeftPosTy (ORightOf '(low,high)) (Str linked minSz maxSz v x r) (PointL O) = TypeError
  (Text "Implement this instance to allow @X -> X str str")

type instance LeftPosTy (OStatic '(low,high)) (Str linked minSz maxSz v x r) (PointL O) = ORightOf '(low+minSz,high+maxSz)


--
--
--TODO for @ORightOf@, we need to make sure we deal with low/high correctly, by moving the k index
--accordingly
--
--TODO this should be @termIx + minSz@ for all cases, while guarding against being over the max
--size
--
--Because we are in a static case, the structure we want to parse goes from @termIx@ to @i-low@. The
--latter is because there could be statically sized objects, say @Chr@ on our RHS.

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O), KnownNat low, KnownNat high, KnownNat minSz
  ) => TermStream m (ps:.OStatic '(low,high)) (TermSymbol ts (Str linked minSz maxSz v x r)) s (is:.PointL O) where
--{{{
  {-# Inline termStream #-}
  termStream Proxy (ts:|Str f xs) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlO synvarIx termIx = getIndex (getIdx s) (Proxy ∷ PRI is (PointL O))
                in  -- traceShow (printf "Str/OStatic %d(%d) synvarIx %d termIx %d" i u synvarIx termIx :: String) $
                    TState s (ii:.:RiPlO synvarIx (synvarIx-low)) (ee:.f xs termIx (synvarIx-low)))
    . termStream (Proxy ∷ Proxy ps) ts us is
    where !low   = fromIntegral . natVal $ Proxy @low
          !high  = fromIntegral . natVal $ Proxy @high
          !minSz = fromIntegral . natVal $ Proxy @minSz
--}}}


instance KnownNat minSz => TermStaticVar (IStatic '(low,high)) (Str linked minSz maxSz v x r) (PointL I) where
--{{{
  termStreamIndex Proxy (Str _ _)   (PointL j)     = PointL j
  termStaticCheck Proxy (Str _ _) _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}
--}}}

instance TermStaticVar (OStatic '(low,high)) (Str linked minSz maxSz v x r) (PointL O) where
  termStreamIndex Proxy (Str _ _)   (PointL j)     = PointL j
  termStaticCheck Proxy (Str _ _) _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

