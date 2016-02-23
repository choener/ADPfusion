
module ADP.Fusion.Term.Chr.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Chr.Type

import           ADP.Fusion.Base.Term



-- | First try in getting this right with a @termStream@.
--
-- TODO use @PointL i@ since this is probably the same for all single-tape
-- instances with @ElmChr@.
--
-- TODO it might even be possible to auto-generate this code via TH.

instance
  ( TmkCtx1 m ls (Chr r x) (PointL i)
  ) => MkStream m (ls :!: Chr r x) (PointL i) where
  mkStream (ls :!: Chr f xs) sv us is
    = S.map (\(ss,ee,ii) -> ElmChr ee ii ss) -- recover ElmChr
    . addTermStream1 (Chr f xs) sv us is
    $ mkStream ls (termStaticVar (Chr f xs) sv is) us (termStreamIndex (Chr f xs) sv is)
  {-# Inline mkStream #-}



-- | Current first try for using @TermStream@
--
-- TODO what happens to fusion if @staticCheck@ happens before @S.map@?
--
-- NOTE / TODO a bit faster with @seq xs@ ?

instance
  ( TstCtx m ts s x0 i0 is (PointL I)
  ) => TermStream m (TermSymbol ts (Chr r x)) s (is:.PointL I) where
  termStream (ts:|Chr f xs) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    -- seq xs . staticCheck (i>0 && i<=u && i<= VG.length xs)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:. f xs (i-1)))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx m ts s x0 i0 is (PointL O)
  ) => TermStream m (TermSymbol ts (Chr r x)) s (is:.PointL O) where
  termStream (ts:|Chr f xs) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlO k o = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.: RiPlO (k+1) o) (ee:.f xs k))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar (Chr r x) (PointL I) where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (PointL j) = PointL $ j-1
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar (Chr r x) (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic (d+1)
  termStreamIndex _ _           j = j
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

