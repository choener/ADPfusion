
{-# LANGUAGE FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language TypeOperators #-}
{-# Language TypeSynonymInstances #-}

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
  , Element ls PointL
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Chr r x) PointL where
  mkStream (ls :!: Chr f xs) (IStatic d) (PointL u) (PointL i)
    = staticCheck (i>0 && i<=u && i<= VG.length xs)
    $ S.map (ElmChr (f xs $ i-1) (PointL $ i) (PointL 0))
    $ mkStream ls (IStatic d) (PointL u) (PointL $ i-1)
  mkStream _ _ _ _ = error "mkStream / Chr / PointL can only be implemented for IStatic"
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: Chr r x) (Outside PointL) where
  mkStream (ls :!: Chr f xs) (OStatic d) (O (PointL u)) (O (PointL i))
    = S.map (\z -> let (O (PointL k)) = getOmx z in ElmChr (f xs $ k-d-1) (O . PointL $ k-d) (getOmx z) z)
    $ mkStream ls (OStatic $ d+1) (O $ PointL u) (O $ PointL i)
  mkStream _ _ _ _ = error "Chr.Point / mkStream / Chr / Outside.PointL can only be implemented for OStatic"
  {-# Inline mkStream #-}

-- TODO @Inline [0]@ ???

instance TermStaticVar (Chr r x) PointL where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (PointL j) = PointL $ j-1
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar (Chr r x) (Outside PointL) where
  termStaticVar   _ (OStatic d) _ = OStatic (d+1) 
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.PointL) where
  terminalStream (a:|Chr f (!v)) (sv:.IStatic _) (is:.i@(PointL j))
    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.f v (j-1)))
    . iPackTerminalStream a sv (is:.i)
    {-
    . terminalStream a sv is
    . S.map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    -}
  terminalStream (a:|Chr f (!v)) (sv:._) (is:.i@(PointL _))
    = S.map (\(S6 s (zi:.PointL k) (zo:.PointL l) is os e) -> S6 s zi zo (is:.PointL (k+1)) (os:.PointL 0) (e:.f v (l-1)))
    . iPackTerminalStream a sv (is:.i)
    {-
    . terminalStream a sv is
    . S.map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
    -}
  {-# INLINE terminalStream #-}

instance
  ( Monad m
  , TerminalStream m a (Outside is)
  , Context (Outside (is:.PointL)) ~ (Context (Outside is) :. OutsideContext Int)
  ) => TerminalStream m (TermSymbol a (Chr r x)) (Outside (is:.PointL)) where
  terminalStream (a:|Chr f (!v)) (sv:.OStatic d) (O (is:.i))
    = S.map (\(S6 s (zi:._) (zo:.(PointL k)) (O is) (O os) e) -> S6 s zi zo (O (is:.(PointL $ k-d))) (O (os:.PointL k)) (e:.f v (k-d-1)))
    . oPackTerminalStream a sv (O (is:.i))
    {-
    . terminalStream a sv (O is)
    . S.map (\(S5 s zi zo (O (is:.i)) (O (os:.o))) -> S5 s (zi:.i) (zo:.o) (O is) (O os))
    -}
  {-
  terminalStream (a:|Chr f (!v)) (sv:._) (is:.PointL i)
    = S.map (\(S6 s (zi:.PointL k) (zo:.PointL l) is os e) -> S6 s zi zo (is:.PointL (k+1)) (os:.PointL 0) (e:.f v (l-1)))
    . terminalStream a sv is
    . S.map (\(S5 s zi zo (is:.i) (os:.o)) -> S5 s (zi:.i) (zo:.o) is os)
  -}
  {-# INLINE terminalStream #-}

