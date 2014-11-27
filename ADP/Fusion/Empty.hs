{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | The 'Empty' terminal symbol parses only the empty (sub-)input. @Empty@
-- however, can mean different things.
--
-- 'Empty' needs to be bound to the input. We require this as certain index
-- structures have no natural notion of emptyness -- unless additional
-- information is given.
--
-- Consider, for example, linear grammars. Left-linear grammars can compare the
-- index @i@ to zero, @i==0@ to test for emptyness, while for right-linear
-- grammars, we need to test @i==N@ with @N@ the size of the input. Instead of
-- carrying @N@ around in the index, we bind the input to @Empty@.
--
-- This choice is currently a bit of a "hunch" but we do have algorithms in
-- mind, where this could be useful.

module ADP.Fusion.Empty where

import           Data.Strict.Maybe
import           Data.Strict.Tuple
import           Prelude hiding (Maybe(..))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR)

import           ADP.Fusion.Classes
import           ADP.Fusion.Multi.Classes



data Empty x = Empty !x

empty = Empty
{-# INLINE empty #-}

instance Build (Empty x)

instance (Element ls Subword) => Element (ls :!: Empty x) Subword where
  data Elm (ls :!: Empty x) Subword = ElmEmpty !Subword !(Elm ls Subword)
  type Arg (ls :!: Empty x)         = Arg ls :. ()
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
  ) => MkStream m (ls :!: Empty x) Subword where
  mkStream (ls :!: Empty _) Static (Subword (i:.j))
    = S.map (ElmEmpty (subword i j))
    $ mkStream ls Static (subword i j)
  mkStream _ _ _ = error "mkStream Empty/Subword called with illegal parameters"
  {-# INLINE mkStream #-}

type instance TermArg (TermSymbol a (Empty x)) = TermArg a :. ()

instance TermStaticVar (Empty x) PointL where
  termStaticVar   _ sv _  = sv
  termStreamIndex _ _  ij = ij
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance TermStaticVar (Empty x) Subword where
    termStaticVar = error "write me"
    termStreamIndex = error "write me"

-- | Again, we assume that no 'staticCheck' is necessary and that @i==j@ is
-- true.

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Empty x)) (is:.PointL) where
  terminalStream (a:>Empty _) (sv:.Static) (is:.PointL (i:.j))
    = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
    . terminalStream a sv is
    . S.map moveIdxTr
  terminalStream _ _ _ = error "mkStream Empty/(is:.PointL) called with illegal parameters"
  {-# INLINE terminalStream #-}

instance
    ( Monad m
    , TerminalStream m a is
    ) => TerminalStream m (TermSymbol a (Empty x)) (is:.Subword) where
      terminalStream (a:>Empty _) (sv:.Static) (is:.Subword (i:.j))
        = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
        . terminalStream a sv is
        . S.map moveIdxTr
      terminalStream _ _ _ = error "mkStream Empty/(is:.Subword) called with illegal parameters"
      {-# INLINE terminalStream #-}


