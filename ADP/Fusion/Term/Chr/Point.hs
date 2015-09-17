
module ADP.Fusion.Term.Chr.Point where

import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Chr.Type


instance
  ( Monad m
  , Element ls (PointL I)
  , MkStream m ls (PointL I)
  ) => MkStream m (ls :!: Chr r x) (PointL I) where
  mkStream (ls :!: Chr f xs) (IStatic d) (PointL u) (PointL i)
    = staticCheck (i>0 && i<=u && i<= VG.length xs)
    $ S.map (ElmChr (f xs $ i-1) (PointL $ i) (PointL 0))
    $ mkStream ls (IStatic d) (PointL u) (PointL $ i-1)
  mkStream _ _ _ _ = error "mkStream / Chr / PointL can only be implemented for IStatic"
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (PointL O)
  , MkStream m ls (PointL O)
  ) => MkStream m (ls :!: Chr r x) (PointL O) where
  mkStream (ls :!: Chr f xs) (OStatic d) (PointL u) (PointL i)
    = S.map (\z -> let (PointL k) = getOmx z in ElmChr (f xs $ k-d-1) (PointL $ k-d) (getOmx z) z)
    $ mkStream ls (OStatic $ d+1) (PointL u) (PointL i)
  mkStream _ _ _ _ = error "Chr.Point / mkStream / Chr / Outside.PointL can only be implemented for OStatic"
  {-# Inline mkStream #-}

-- TODO @Inline [0]@ ???

instance TermStaticVar (Chr r x) (PointL I) where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (PointL j) = PointL $ j-1
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar (Chr r x) (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic (d+1) 
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.PointL I) where
  terminalStream (a:|Chr f (!v)) (sv:.IStatic _) (is:.i@(PointL j))
    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.f v (j-1)))
    . iPackTerminalStream a sv (is:.i)
    {-
    . terminalStream a sv is
    . S.map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    -}
  terminalStream (a:|Chr f (!v)) (sv:._) (is:.i@(PointL _))
    = S.map (\(S6 s (zi:.PointL k) (zo:.PointL l) is os e) -> S6 s zi zo (is:.PointL (k+1)) (os:.PointL 0) (e:.f v (l-1))) -- TODO is the @l-1@ even right? is this part even called?
    . iPackTerminalStream a sv (is:.i)
    {-
    . terminalStream a sv is
    . S.map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    -}
  {-# INLINE terminalStream #-}

instance
  ( Monad m
  , TerminalStream m a is
--  , Context (Outside (is:.PointL)) ~ (Context (Outside is) :. OutsideContext Int)
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.PointL O) where
  terminalStream (a:|Chr f (!v)) (sv:.OStatic d) (is:.i)
    = S.map (\(S6 s (zi:._) (zo:.(PointL k)) is os e) -> S6 s zi zo (is:.(PointL $ k-d)) (os:.PointL k) (e:.f v (k-d-1)))
    . iPackTerminalStream a sv (is:.i)
  {-
  terminalStream (a:|Chr f (!v)) (sv:._) (is:.PointL i)
    = S.map (\(S6 s (zi:.PointL k) (zo:.PointL l) is os e) -> S6 s zi zo (is:.PointL (k+1)) (os:.PointL 0) (e:.f v (l-1)))
    . terminalStream a sv is
    . S.map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
  -}
  {-# INLINE terminalStream #-}

