{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Empty where

import Data.Array.Repa.Index
import Data.Strict.Maybe
import Data.Strict.Tuple
import Prelude hiding (Maybe(..))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Points

import ADP.Fusion.Classes
import ADP.Fusion.Multi.Classes



data Empty = Empty

empty = Empty
{-# INLINE empty #-}

instance Build Empty

instance (Element ls Subword) => Element (ls :!: Empty) Subword where
  data Elm (ls :!: Empty) Subword = ElmEmpty !Subword !(Elm ls Subword)
  type Arg (ls :!: Empty)         = Arg ls :. ()
  getArg (ElmEmpty _ l) = getArg l :. ()
  getIdx (ElmEmpty i _) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- | Empty as an argument only makes sense if empty is static. We don't get to
-- use 'staticCheck' as the underlying check for the bottom of the argument
-- stack should take care of the @i==j@ check.

instance
  ( Monad m
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Empty) Subword where
  mkStream (ls :!: Empty) Static (Subword (i:.j))
    = S.map (ElmEmpty (subword i j))
    $ mkStream ls Static (subword i j)
  mkStream _ _ _ = error "mkStream Empty/Subword called with illegal parameters"
  {-# INLINE mkStream #-}

type instance TermArg (TermSymbol a Empty) = TermArg a :. ()

instance TermStaticVar Empty PointL where
  termStaticVar   _ sv _  = sv
  termStreamIndex _ _  ij = ij
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

-- | Again, we assume that no 'staticCheck' is necessary and that @i==j@ is
-- true.

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Empty) (is:.PointL) where
  terminalStream (a:>Empty) (sv:.Static) (is:.PointL (i:.j))
    = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
    . terminalStream a sv is
    . S.map moveIdxTr
  terminalStream _ _ _ = error "mkStream Empty/(is:.PointL) called with illegal parameters"
  {-# INLINE terminalStream #-}

