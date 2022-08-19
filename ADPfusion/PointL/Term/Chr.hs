
module ADPfusion.PointL.Term.Chr where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import           GHC.Exts
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           Text.Printf

import           Data.PrimitiveArray
import           Data.Ord.Fast

import           ADPfusion.Core
import           ADPfusion.Core.Term.Chr
import           ADPfusion.PointL.Core



type instance LeftPosTy (IStatic d) (Chr r x) (PointL I) = IStatic d
--type instance LeftPosTy (IVariable d) (Chr r x) (PointL I) = IVariable d

type instance LeftPosTy (OStatic '(low,high)) (Chr r x) (PointL O) = OStatic '(low+1,high+1)

-- | First try in getting this right with a @termStream@.
--
-- TODO use @PointL i@ since this is probably the same for all single-tape
-- instances with @ElmChr@.
--
-- TODO it might even be possible to auto-generate this code via TH.

instance
  forall pos posLeft m ls r x i
  . ( TermStream m (Z:.pos) (TermSymbol M (Chr r x)) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos (Chr r x) (PointL i)
    , TermStaticVar pos (Chr r x) (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  ⇒ MkStream m pos (ls :!: Chr r x) (PointL i) where
  mkStream pos (ls :!: Chr f xs) grd us is
    = S.map (\(ss,ee,ii) -> ElmChr ee ii ss) -- recover ElmChr
    . addTermStream1 pos (Chr f xs) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos (Chr f xs) us is grd) us (termStreamIndex pos (Chr f xs) is)
  {-# Inline mkStream #-}


-- | 

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts (Chr r x)) s (is:.PointL I) where
  termStream Proxy (ts:|Chr f xs) (us:..LtPointL u) (is:.PointL i)
    -- NOTE changing from @f xs (i-1)@ to @f xs $! i-1@, forcing @i-1@ first,
    -- yielding 50% better performance in Needleman-Wunsch
    --
    -- NOTE the @let ... in@ part, in principle, requires that @xs@ contains at least one element,
    -- at index 0. In case of empty inputs, this will be violated and we should check that nothing
    -- breaks. Compare performance of this version vs. the inline version. Inline also does not need
    -- @clamp@, but currently always evaluates @e@, even if the value is not actually needed.
    = S.map (\(TState s ii ee) -> let !e = f xs $! i-1 in TState s (ii:.:RiPlI i) (ee:.e))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O), KnownNat low, KnownNat high
  ) => TermStream m (ps:.OStatic '(low,high)) (TermSymbol ts (Chr r x)) s (is:.PointL O) where
  termStream Proxy (ts:|Chr f xs) (us:..LtPointL u) (is:.PointL i)
    = let !low  :: Int = fromIntegral $ natVal (Proxy @low)
          !high :: Int = fromIntegral $ natVal (Proxy @high)
    in S.map (\(TState s ii ee) ->
                let RiPlO synvarIx termIx = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  traceShow (printf "Chr/OStatic @ %d, synvarIx %d, termIx %d" i synvarIx termIx :: String) $
                    TState s (ii:.: RiPlO synvarIx (termIx+1)) (ee:.f xs termIx))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



instance TermStaticVar (IStatic d) (Chr r x) (PointL I) where
  termStreamIndex Proxy (Chr f x) (PointL j) = PointL $! j-1
  termStaticCheck Proxy (Chr f x) _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (OStatic d) (Chr r x) (PointL O) where
  termStreamIndex Proxy (Chr f x) (PointL j) = PointL $ j
  termStaticCheck Proxy (Chr f x) _ (PointL j) grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

