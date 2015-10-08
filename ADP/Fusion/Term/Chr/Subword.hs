
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
  ( Monad m
  , MkStream m ls (Subword i)
  , TermStream m (TermSymbol M (Chr r x)) (Z:.Subword i) (Z:.Subword i)
  , Element ls (Subword i)
  , TermStaticVar (Chr r x) (Subword i)
  ) => MkStream m (ls :!: Chr r x) (Subword i) where
  mkStream (ls :!: Chr f xs) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmChr ee ii oo ss)
    . addTermStream1 (Chr f xs) sv us is
    $ mkStream ls (termStaticVar (Chr f xs) sv is) us (termStreamIndex (Chr f xs) sv is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , TermStream m ts a is
  , GetIndex a (is:.Subword I)
  , GetIx a (is:.Subword I) ~ (Subword I)
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
  ( Monad m
  , TermStream m ts a is
  , GetIndex a (is:.Subword O)
  , GetIx a (is:.Subword O) ~ (Subword O)
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

--instance
--  ( Monad m
--  , Element ls (Subword I)
--  , MkStream m ls (Subword I)
--  ) => MkStream m (ls :!: Chr r x) (Subword I) where
--  mkStream (ls :!: Chr f xs) (IStatic ()) hh (Subword (i:.j))
--    = staticCheck (i>=0 && i<j && j<= VG.length xs)
--    $ map (ElmChr (f xs $ j-1) (subword (j-1) j) (subword 0 0))
--    $ mkStream ls (IStatic ()) hh (delay_inline Subword (i:.j-1))
--  mkStream (ls :!: Chr f xs) (IVariable ()) hh (Subword (i:.j))
--    = map (\s -> let Subword (_:.l) = getIdx s
--                 in  ElmChr (f xs l) (subword l (l+1)) (subword 0 0) s)
--    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j-1))
--  {-# Inline mkStream #-}

--instance
--  ( Monad m
--  , Element ls (Subword O)
--  , MkStream m ls (Subword O)
--  ) => MkStream m (ls :!: Chr r x) (Subword O) where
--  mkStream (ls :!: Chr f xs) (OStatic (di:.dj)) u ij@(Subword (i:.j))
--    = id -- staticCheck ( j < h ) -- TODO any check possible?
--    $ map (\s -> let (Subword (_:.k')) = getIdx s
--                     k = k'-dj -- -1
--                 in  ElmChr (f xs k) (subword (k'-1) k') (getOmx s) s)
--    $ mkStream ls (OStatic (di:.dj+1)) u ij
--  mkStream (ls :!: Chr f xs) (ORightOf (di:.dj)) u ij
--    = map (\s -> let (Subword (_:.k')) = getIdx s
--                     k = k'-dj-1
--                 in  ElmChr (f xs k) (subword (k'-1) k') (getOmx s) s)
--    $ mkStream ls (ORightOf (di:.dj+1)) u ij
--  mkStream (ls :!: Chr f xs) (OFirstLeft (di:.dj)) u ij
--    = id
--    $ map (\s -> let (Subword (_:.k)) = getIdx s
--                 in  ElmChr (f xs k) (subword k (k+1)) (getOmx s) s)
--    $ mkStream ls (OFirstLeft (di+1:.dj)) u ij
--  mkStream (ls :!: Chr f xs) (OLeftOf (di:.dj)) u ij
--    = map (\s -> let (Subword (_:.k)) = getIdx s
--                 in  ElmChr (f xs k) (subword k (k+1)) (getOmx s) s)
--    $ mkStream ls (OLeftOf (di+1:.dj)) u ij
--  {-# Inline mkStream #-}



--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.Subword I) where
--  terminalStream (a:|Chr f v) (sv:.IStatic _) (is:.ix@(Subword (i:.j)))
--    -- TODO check if 'staticCheck' breaks fusion!!!
--    = staticCheck (i>=0 && i<j && j<=VG.length v)
--    . S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.subword (j-1) j) (os:.subword 0 0) (e:.f v (j-1)))
--    . iPackTerminalStream a sv (is:.ix)
--  terminalStream (a:|Chr f v) (sv:.IVariable _) (is:.ix@(Subword (i:.j)))
--    = S.map (\(S6 s (zi:.Subword (_:.l)) (zo:._) is os e) -> S6 s zi zo (is:.subword l (l+1)) (os:.subword 0 0) (e:.f v l))
--    . iPackTerminalStream a sv (is:.ix)
--  {-# Inline terminalStream #-}

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

