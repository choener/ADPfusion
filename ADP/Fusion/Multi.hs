{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | The multi-tape extension of ADPfusion.

module ADP.Fusion.Multi where

import Data.Array.Repa.Index
import Data.Strict.Tuple

import ADP.Fusion.Classes

-- import Data.Array.Repa.Index.Subword



--
--
-- TODO check if this is fused away

data Term a b where
  T    :: Term a b
  (:!) :: !(Term a b) -> !c -> Term (Term a b) c

instance Build (Term a b)

instance
  ( ValidIndex ls ix
  ) => ValidIndex (ls :!: Term a b) ix where
  validIndex (ls :!: t) abc ix =
    allDimensionsValid t abc ix && validIndex ls abc ix
  {-# INLINE validIndex #-}
  getParserRange (ls :!: t) ix = undefined





type instance ParserRange Z = Z
type instance ParserRange (tail:.head) = ParserRange tail :. ParserRange head

