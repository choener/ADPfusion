
-- | TODO if we have a table that has min-size @>0@ we need to immediately
-- terminate @addIndexDenseGo@ !

module ADP.Fusion.SynVar.Indices.Unit where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Unit I)
  , GetIx a (is:.Unit I) ~ (Unit I)
  ) => AddIndexDense a (us:.Unit I) (is:.Unit I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:._) (is:._)
    = map (\(SvS s a b t y' z') -> SvS s a b (t:.Unit) (y':.Unit) (z':.Unit))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Unit O)
  , GetIx a (is:.Unit O) ~ (Unit O)
  ) => AddIndexDense a (us:.Unit O) (is:.Unit O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:._) (is:._)
    = map (\(SvS s a b t y' z') -> SvS s a b (t:.Unit) (y':.Unit) (z':.Unit))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Unit C)
  , GetIx a (is:.Unit C) ~ (Unit C)
  ) => AddIndexDense a (us:.Unit I) (is:.Unit C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:._) (is:._)
    = map (\(SvS s a b t y' z') -> SvS s a b (t:.Unit) (y':.Unit) (z':.Unit))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Unit C)
  , GetIx a (is:.Unit C) ~ (Unit C)
  ) => AddIndexDense a (us:.Unit O) (is:.Unit C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:._) (is:._)
    = map (\(SvS s a b t y' z') -> SvS s a b (t:.Unit) (y':.Unit) (z':.Unit))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

