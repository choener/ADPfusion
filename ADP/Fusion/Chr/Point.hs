
{-# LANGUAGE FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language TypeOperators #-}
{-# Language TypeSynonymInstances #-}

module ADP.Fusion.Chr.Point where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Chr.Type


instance
  ( Monad m
  , Element ls PointL
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Chr r x) PointL where
  mkStream (ls :!: Chr f xs) IStatic (PointL u) (PointL i)
    = staticCheck (i>0 && i<=u && i<= VG.length xs)
    $ S.map (ElmChr (f xs $ i-1) (PointL $ i) (PointL 0))
    $ mkStream ls IStatic (PointL u) (PointL $ i-1)
  mkStream _ _ _ _ = error "mkStream / Chr / PointL can only be implemented for IStatic"
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: Chr r x) (Outside PointL) where
  mkStream (ls :!: Chr f xs) (OStatic d) (O (PointL u)) (O (PointL i))
    = staticCheck (i>d && i<=u && i<= VG.length xs)
    $ S.map (\z -> let (O (PointL k)) = getOmx z in ElmChr (f xs $ k-d-1) (O . PointL $ k-d) (getOmx z) z)
    $ mkStream ls (OStatic $ d+1) (O $ PointL u) (O $ PointL i)
  mkStream _ _ _ _ = error "mkStream / Chr / PointL can only be implemented for OStatic"
  {-# Inline mkStream #-}

