{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module ADP.Fusion.TH.Test where

import           Data.List
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM

import           ADP.Fusion.TH



data Bla m a b c x r = Bla
  { fun1 :: a           -> x
  , fun2 :: a -> b      -> x
  , fun3 :: a -> x -> c -> x
  , h    :: SM.Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Bla

