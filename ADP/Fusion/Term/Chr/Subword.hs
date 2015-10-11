
module ADP.Fusion.Term.Chr.Subword where

import           Data.Proxy
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import           Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           Prelude hiding (map)

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Chr.Type



instance
  ( TmkCtx1 m ls (Chr r x) (Subword i)
  ) => MkStream m (ls :!: Chr r x) (Subword i) where
  mkStream (ls :!: Chr f xs) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmChr ee ii oo ss)
    . addTermStream1 (Chr f xs) sv us is
    $ mkStream ls (termStaticVar (Chr f xs) sv is) us (termStreamIndex (Chr f xs) sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (Subword I)
  ) => TermStream m (TermSymbol ts (Chr r x)) a (is:.Subword I) where
  termStream (ts:|Chr f xs) (cs:.IStatic ()) (us:.u) (is:.Subword (i:.j))
    = staticCheck (i>=0 && i < j && j <= VG.length xs)
    . map (\(TState s a b ii oo ee) ->
              TState s a b (ii:.subword (j-1) j) (oo:.subword 0 0) (ee:.f xs (j-1)) )
    . termStream ts cs us is
  --
  termStream (ts:|Chr f xs) (cs:.IVariable ()) (us:.u) (is:.Subword (i:.j))
    = map (\(TState s a b ii oo ee) ->
              let Subword (_:.l) = getIndex a (Proxy :: Proxy (is:.Subword I))
              in  TState s a b (ii:.subword l (l+1)) (oo:.subword 0 0) (ee:.f xs l) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (Subword O)
  ) => TermStream m (TermSymbol ts (Chr r x)) a (is:.Subword O) where
  termStream (ts:|Chr f xs) (cs:.OStatic (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = map (\(TState s a b ii oo ee) ->
              let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                  o              = getIndex b (Proxy :: Proxy (is:.Subword O))
                  l              = k - dj
              in  TState s a b (ii:.subword k (k+1)) (oo:.o) (ee:.f xs k) )
    . termStream ts cs us is
  --
  termStream (ts:|Chr f xs) (cs:.ORightOf (di:.dj)) (us:.u) (is:.i)
    = map (\(TState s a b ii oo ee) ->
              let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                  o              = getIndex b (Proxy :: Proxy (is:.Subword O))
                  l              = k - dj - 1
              in  TState s a b (ii:.subword (k-1) k) (oo:.o) (ee:.f xs l) )
    . termStream ts cs us is
  --
  termStream (ts:|Chr f xs) (cs:.OFirstLeft (di:.dj)) (us:.u) (is:.i)
    = map (\(TState s a b ii oo ee) ->
              let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                  o              = getIndex b (Proxy :: Proxy (is:.Subword O))
              in  TState s a b (ii:.subword k (k+1)) (oo:.o) (ee:.f xs k) )
    . termStream ts cs us is
  --
  termStream (ts:|Chr f xs) (cs:.OLeftOf (di:.dj)) (us:.u) (is:.i)
    = map (\(TState s a b ii oo ee) ->
              let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                  o              = getIndex b (Proxy :: Proxy (is:.Subword O))
              in  TState s a b (ii:.subword k (k+1)) (oo:.o) (ee:.f xs k) )
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar (Chr r x) (Subword I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (Subword (i:.j)) = subword i (j-1)
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar (Chr r x) (Subword O) where
  termStaticVar _ (OStatic    (di:.dj)) _ = OStatic    (di  :.dj+1)
  termStaticVar _ (ORightOf   (di:.dj)) _ = ORightOf   (di  :.dj+1)
  termStaticVar _ (OFirstLeft (di:.dj)) _ = OFirstLeft (di+1:.dj  )
  termStaticVar _ (OLeftOf    (di:.dj)) _ = OLeftOf    (di+1:.dj  )
  termStreamIndex _ _ sw = sw
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

