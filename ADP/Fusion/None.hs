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

import ADP.Fusion.Classes



data None = None

none = None
{-# INLINE none #-}

-- None is always valid

instance
  ( ValidIndex ls Subword
  ) => ValidIndex (ls :!: None) Subword where
    validIndex (ls:!:None) abc ij@(Subword (i:.j)) = validIndex ls abc ij
    {-# INLINE validIndex #-}

instance Build None

instance
  ( Elms ls Subword
  ) => Elms (ls :!: None) Subword where
  data Elm (ls :!: None) Subword = ElmNone !(Elm ls Subword) !() !Subword
  type Arg (ls :!: None) = Arg ls :. ()
  getArg !(ElmNone ls () _) = getArg ls :. ()
  getIdx !(ElmNone _ _ i)   = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:None) Subword where
  mkStream !(ls:!:None) Outer !ij@(Subword (i:.j))
    = S.map (\s -> ElmNone s () (subword i j))
    $ S.filter (\_ -> i==j)
    $ mkStream ls Outer ij
  {-# INLINE mkStream #-}

