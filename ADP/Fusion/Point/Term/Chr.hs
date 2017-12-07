
module ADP.Fusion.Point.Term.Chr where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           GHC.Exts

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Point.Core
import           ADP.Fusion.Term.Chr.Type



type instance LeftPosTy (IStatic d) (Chr r x) (PointL I) = IStatic d

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
    $ mkStream (Proxy ∷ Proxy posLeft) ls (grd `andI#` termStaticCheck pos (Chr f xs) is) us (termStreamIndex pos (Chr f xs) is)
  {-# Inline mkStream #-}


-- | 

instance
  ( TstCtx m ps ts s x0 i0 is (PointL I)
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts (Chr r x)) s (is:.PointL I) where
  termStream Proxy (ts:|Chr f xs) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:. f xs (i-1)))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

{-
instance
  ( TstCtx m ts s x0 i0 is (PointL O)
  ) => TermStream m (TermSymbol ts (Chr r x)) s (is:.PointL O) where
  termStream (ts:|Chr f xs) (cs:.OStatic d) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlO k o = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.: RiPlO (k+1) o) (ee:.f xs k))
    . termStream ts cs us is
  {-# Inline termStream #-}
-}


instance TermStaticVar (IStatic d) (Chr r x) (PointL I) where
  termStreamIndex Proxy (Chr f x) (PointL j) = PointL $ j-1
  termStaticCheck Proxy (Chr f x) (PointL j) = 1#
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

{-
instance TermStaticVar (Chr r x) (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic (d+1)
  termStreamIndex _ _           j = j
  termStaticCheck _ _ = 1#
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}
-}

