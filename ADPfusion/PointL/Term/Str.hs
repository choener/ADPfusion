
module ADPfusion.PointL.Term.Str where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import           GHC.Exts
import           Data.Type.Equality
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Str
import           ADPfusion.PointL.Core



-- minSz done via TermStaticVar ?!

type instance LeftPosTy (IStatic   d) (Str linked minSz maxSz v x r) (PointL I) = IVariable d
type instance LeftPosTy (IVariable d) (Str linked minSz maxSz v x r) (PointL I) = IVariable d

type instance LeftPosTy (OStatic d) (Str linked minSz maxSz v x r) (PointL O) = ORightOf d
type instance LeftPosTy (ORightOf d) (Str linked minSz maxSz v x r) (PointL O) = TypeError
  (Text "Implement this instance to allow @X -> X str str")


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
  mkStream pos (ls :!: Str f xs) grd us is
    = S.map (\(ss,ee,ii) -> ElmStr ee ii ss) -- recover ElmChr
    . addTermStream1 pos (Str @v @x @r @linked @minSz @maxSz f xs) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls
               (termStaticCheck pos (Str @v @x @r @linked @minSz @maxSz f xs) us is grd)
               us (termStreamIndex pos (Str @v @x @r @linked @minSz @maxSz f xs) is)
  {-# Inline mkStream #-}
--}}}

-- | Note that the @minSz@ should automatically work out due to the encoding in
-- @d@.
--
-- TODO handle minSz/maxSz

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  , MaybeMaxSz maxSz
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts (Str linked minSz maxSz v x r)) s (is:.PointL I) where
  termStream Proxy (ts:|Str f xs) (us:..LtPointL u) (is:.PointL i)
    = S.mapMaybe (\(TState s ii ee) ->
                let RiPlI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointL I))
                in  maybeMaxSz (Proxy @maxSz) (i-k) $ TState s (ii:.:RiPlI i) (ee:.f xs k i))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O), MaybeMaxSz maxSz
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts (Str linked minSz maxSz v x r)) s (is:.PointL O) where
--{{{
--TODO still horribly wrong!
  {-# Inline termStream #-}
  termStream Proxy (ts:|Str f xs) (us:..LtPointL u) (is:.PointL i)
    = S.mapMaybe (\(TState s ii ee) ->
                let RiPlO k o = getIndex (getIdx s) (Proxy ∷ PRI is (PointL O))
                in  traceShow ("wrong",i,k,o) . maybeMaxSz (Proxy @maxSz) (i-k) $ TState s (ii:.:RiPlO (k+1) o) (ee:.f xs k i))
    . termStream (Proxy ∷ Proxy ps) ts us is
--}}}


instance KnownNat minSz => TermStaticVar (IStatic d) (Str linked minSz maxSz v x r) (PointL I) where
--{{{
  termStreamIndex Proxy (Str _ _)   (PointL j)     = PointL $ j - fromIntegral (natVal (Proxy ∷ Proxy minSz))
  termStaticCheck Proxy (Str _ _) _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}
--}}}

instance KnownNat minSz => TermStaticVar (OStatic d) (Str linked minSz maxSz v x r) (PointL O) where
  termStreamIndex Proxy (Str _ _)   (PointL j)     = PointL $ j -- - fromIntegral (natVal (Proxy ∷ Proxy minSz))
  termStaticCheck Proxy (Str _ _) _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

