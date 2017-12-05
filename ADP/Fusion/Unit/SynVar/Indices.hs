
-- | TODO if we have a table that has min-size @>0@ we need to immediately
-- terminate @addIndexDenseGo@ !

module ADP.Fusion.Unit.SynVar.Indices where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core
import ADP.Fusion.Unit.Core



instance
  ( IndexHdr s x0 i0 us (Unit I) cs c is (Unit I)
  ) => AddIndexDense s (us:.Unit I) (cs:.c) (is:.Unit I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (Unit O) cs c is (Unit O)
  ) => AddIndexDense s (us:.Unit O) (cs:.c) (is:.Unit O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (Unit I) cs c is (Unit C)
  ) => AddIndexDense s (us:.Unit I) (cs:.c) (is:.Unit C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (Unit O) cs c is (Unit C)
  ) => AddIndexDense s (us:.Unit O) (cs:.c) (is:.Unit C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo cs vs ubs us is
  {-# Inline addIndexDenseGo #-}

