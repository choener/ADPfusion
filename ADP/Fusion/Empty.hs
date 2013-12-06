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

import ADP.Fusion.Classes



data Empty = Empty

empty = Empty
{-# INLINE empty #-}

instance
  ( ValidIndex ls Subword
  ) => ValidIndex (ls :!: Empty) Subword where
    validIndex (ls:!:Empty) abc ij@(Subword (i:.j)) = i==j && validIndex ls abc ij
    {-# INLINE validIndex #-}

instance Build Empty

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Empty) Subword where
  data Elm (ls :!: Empty) Subword = ElmEmpty !(Elm ls Subword) !() !Subword
  type Arg (ls :!: Empty) = Arg ls :. ()
  getArg !(ElmEmpty ls () _) = getArg ls :. ()
  getIdx !(ElmEmpty _ _ i)   = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Empty) Subword where
  mkStream !(ls:!:Empty) Outer !ij@(Subword (i:.j))
    = S.map (\s -> ElmEmpty s () (subword i j))
    $ S.filter (\_ -> i==j)
    $ mkStream ls Outer ij
  {-# INLINE mkStream #-}

