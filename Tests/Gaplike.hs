{-# LANGUAGE NoMonomorphismRestriction #-}

-- | A mini-example showing how to use the new GAPlike-version of ADP together
-- with algebra products.
--
-- TODO if we use the NoMono, do we happen to be in the forall m case where
-- optimization doesn't happen?

module Tests.Gaplike where

import Data.Vector.Fusion.Stream.Monadic as SM
import ADP.Fusion.GAPlike
import Prelude as P



-- | Very simple grammar.

gSimple (empty,pair,h) tbl c e = 
  (tbl, empty <<< e           |||
        pair  <<< c % tbl % c ... h)
{-# INLINE gSimple #-}

-- | Simple scoring system

aMax = (empty,pair,h) where
  empty _ = 0
  pair l x r = if l==r then x+1 else x
  h = SM.foldl' max 0

-- | Pretty Printer

aPretty = (empty,pair,h) where
  empty _ = ""
  pair l x r = if l==r then "<" P.++ x P.++ ">" else "." P.++ x P.++ "."
  h = id

-- | Algebra product with three algebras.
--
-- We use the first algebra to filter results (this could be stochastic
-- backtracking, for example). The second and third combine to produce results.
--
-- TODO this should actually be (algF <** (algS *** algT))

aProd f sf ss = (empty,pair,h) where
  (emptyF,pairF,hF) = f
  (emptySF,pairSF,hSF) = sf
  (emptySS,pairSS,hSS) = ss
  empty e = undefined
  pair = undefined
  h = undefined
