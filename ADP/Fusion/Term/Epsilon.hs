
module ADP.Fusion.Term.Epsilon
  ( module ADP.Fusion.Term.Epsilon.Type
  , module ADP.Fusion.Term.Epsilon.Point
  , module ADP.Fusion.Term.Epsilon.Subword
  ) where

import ADP.Fusion.Term.Epsilon.Point
import ADP.Fusion.Term.Epsilon.Subword
import ADP.Fusion.Term.Epsilon.Type

{-

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
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

module ADP.Fusion.Term.Empty where

import           Data.Strict.Maybe
import           Prelude hiding (Maybe(..))

import           Data.PrimitiveArray -- (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR, Outside(..))

import           ADP.Fusion.Term.Classes
import           ADP.Fusion.Term.Multi.Classes

import           Debug.Trace



-- | Empty as an argument only makes sense if empty is static. We don't get to
-- use 'staticCheck' as the underlying check for the bottom of the argument
-- stack should take care of the @i==j@ check.

{-
instance
  ( Monad m
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Empty) Subword where
  mkStream (ls :!: Empty) Static lu (Subword (i:.j))
    = S.map (ElmEmpty (subword i j))
    $ mkStream ls Static lu (subword i j)
  mkStream _ _ _ _ = error "mkStream Empty/Subword called with illegal parameters"
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: Empty) (Outside Subword) where
  mkStream (ls :!: Empty) Static lu (O (Subword (i:.j)))
    = S.map (ElmEmpty (O $ subword i j))
    $ mkStream ls Static lu (O $ subword i j)
  mkStream _ _ _ _ = error "mkStream Empty/Subword called with illegal parameters"
  {-# INLINE mkStream #-}
-}

type instance TermArg (TermSymbol a Empty) = TermArg a :. ()

instance TermStaticVar Empty PointL where
  termStaticVar   _ sv _  = sv
  termStreamIndex _ _  ij = ij
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

{-
instance TermStaticVar Empty Subword where
    termStaticVar = error "write me"
    termStreamIndex = error "write me"
-}

-- | Again, we assume that no 'staticCheck' is necessary and that @i==j@ is
-- true.

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a Empty) (is:.PointL) where
  terminalStream (a:|Empty) (sv:.Static) (is:.PointL (i:.j))
    = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
    . terminalStream a sv is
    . S.map moveIdxTr
  terminalStream _ _ _ = error "mkStream Empty/(is:.PointL) called with illegal parameters"
  {-# INLINE terminalStream #-}

{-
instance
    ( Monad m
    , TerminalStream m a is
    ) => TerminalStream m (TermSymbol a Empty) (is:.Subword) where
      terminalStream (a:>Empty) (sv:.Static) (is:.Subword (i:.j))
        = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
        . terminalStream a sv is
        . S.map moveIdxTr
      terminalStream _ _ _ = error "mkStream Empty/(is:.Subword) called with illegal parameters"
      {-# INLINE terminalStream #-}
-}

-}

