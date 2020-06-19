
module ADPfusion.PointL.Term.Switch where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Switch
import           ADPfusion.PointL.Core



type instance LeftPosTy (IStatic   d) Switch (PointL I) = IStatic   d
type instance LeftPosTy (IVariable d) Switch (PointL I) = IVariable d

type instance LeftPosTy (OStatic d) Switch (PointL O) = OStatic d

-- | 

instance
  forall pos posLeft m ls r x i
  . ( TermStream m (Z:.pos) (TermSymbol M Switch) (Elm (Term1 (Elm ls (PointL i))) (Z :. PointL i)) (Z:.PointL i)
    , posLeft ~ LeftPosTy pos Switch (PointL i)
    , TermStaticVar pos Switch (PointL i)
    , MkStream m posLeft ls (PointL i)
    )
  ⇒ MkStream m pos (ls :!: Switch) (PointL i) where
  mkStream pos (ls :!: Switch s) grd us is
    = S.map (\(ss,ee,ii) -> ElmSwitch ii ss) -- recover ElmChr
    . addTermStream1 pos (Switch s) us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos (Switch s) us is grd) us (termStreamIndex pos (Switch s) is)
  {-# Inline mkStream #-}


-- | 

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL I)
  ) => TermStream m (ps:.IStatic d) (TermSymbol ts Switch) s (is:.PointL I) where
  termStream Proxy (ts:|Switch s) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:. ()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance
  ( TermStreamContext m ps ts s x0 i0 is (PointL O)
  ) => TermStream m (ps:.OStatic d) (TermSymbol ts Switch) s (is:.PointL O) where
  termStream Proxy (ts:|Switch s) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let ko = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.:ko) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}



instance TermStaticVar (IStatic d) Switch (PointL I) where
  termStreamIndex Proxy (Switch s) (PointL j) = PointL $ j
  -- TODO is trac #15696 a problem here?
  termStaticCheck Proxy (Switch s) _ (PointL j) grd = dataToTag# s `andI#` grd -- case s of {Enabled → grd; Disabled → 0# }
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar (OStatic d) Switch (PointL O) where
  termStreamIndex Proxy (Switch s) (PointL j) = PointL $ j
  termStaticCheck Proxy (Switch s) _ (PointL j) grd = case s of {Enabled → grd; Disabled → 0# }
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

