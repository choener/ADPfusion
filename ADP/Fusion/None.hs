{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.None where

import Data.Array.Repa.Index
import Data.Strict.Maybe
import Data.Strict.Tuple
import Prelude hiding (Maybe(..))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Points

import ADP.Fusion.Classes
import ADP.Fusion.Multi.Classes



data None = None


none = None
{-# INLINE none #-}

instance Build None

type instance TermArg (TermSymbol a None) = TermArg a :. ()

-- | Since 'None' doesn't really do anything for all indices, we just thread it
-- through.

instance TermStaticVar None ix where
  termStaticVar   _ sv _  = sv
  termStreamIndex _ _  ij = ij
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a None) (is:.PointL) where
  terminalStream (a:>None) (sv:._) (is:._)
    = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
    . terminalStream a sv is
    . S.map moveIdxTr
  {-# INLINE terminalStream #-}



-- * Single dimensional instances for 'None' are really weird

instance Element ls Subword => Element (ls :!: None) Subword where
  data Elm (ls :!: None) Subword = ElmNone !Subword !(Elm ls Subword)
  type Arg (ls :!: None)         = Arg ls :. ()
  getArg (ElmNone _ l) = getArg l :. ()
  getIdx (ElmNone i _) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- | The instance does nothing (except insert @()@ into the argument
-- stack).

instance
  ( Monad m
  , MkStream m ls Subword
  ) => MkStream m (ls :!: None) Subword where
  mkStream (ls :!: None) sv ij
    = S.map (ElmNone ij)
    $ mkStream ls sv ij
  {-# INLINE mkStream #-}

