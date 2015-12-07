
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
  ( IndexHdr a us (Unit I) cs c is (Unit I)
  ) => AddIndexDense a (us:.Unit I) (cs:.c) (is:.Unit I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:._) (is:._)
    = map (\(SvS s a t y') -> SvS s a (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (Unit O) cs c is (Unit O)
  ) => AddIndexDense a (us:.Unit O) (cs:.c) (is:.Unit O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:._) (is:._)
    = map (\(SvS s a t y') -> SvS s a (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (Unit I) cs c is (Unit C)
  ) => AddIndexDense a (us:.Unit I) (cs:.c) (is:.Unit C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:._) (is:._)
    = map (\(SvS s a t y') -> SvS s a (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr a us (Unit O) cs c is (Unit C)
  ) => AddIndexDense a (us:.Unit O) (cs:.c) (is:.Unit C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:._) (is:._)
    = map (\(SvS s a t y') -> SvS s a (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

