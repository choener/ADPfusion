
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
  ( IndexHdr ps s x0 i0 us (Unit I) cs c is (Unit I)
  , AddIndexDense ps (Elm x0 i0) cs us is
  )
  ⇒ AddIndexDense ('(:.) ps p) s (cs:.c) (us:.Unit I) (is:.Unit I) where
  addIndexDenseGo Proxy (cs:._) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr ps s x0 i0 us (Unit O) cs c is (Unit O)
  , AddIndexDense ps (Elm x0 i0) cs us is
  )
  ⇒ AddIndexDense ('(:.) ps p) s (cs:.c) (us:.Unit O) (is:.Unit O) where
  addIndexDenseGo Proxy (cs:._) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr ps s x0 i0 us (Unit I) cs c is (Unit C)
  , AddIndexDense ps (Elm x0 i0) cs us is
  )
  ⇒ AddIndexDense ('(:.) ps p) s (cs:.c) (us:.Unit I) (is:.Unit C) where
  addIndexDenseGo Proxy (cs:._) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr ps s x0 i0 us (Unit O) cs c is (Unit C)
  , AddIndexDense ps (Elm x0 i0) cs us is
  )
  ⇒ AddIndexDense ('(:.) ps p) s (cs:.c) (us:.Unit O) (is:.Unit C) where
  addIndexDenseGo Proxy (cs:._) (ubs:.._) (us:.._) (is:._)
    = map (\(SvS s t y') -> SvS s (t:.Unit) (y':.:RiU))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

