
-- | This exports everything needed for sequence-based alignment style
-- algorithms.
--
-- Here are some notes on implementation of the Inside and Outside 
--
-- X_j     -> S_{j-1} X_{j-1} c_j
-- Y_{j-1} -> S_?     X_j     c_j
-- Y_j     -> S_{j+1} X_{j+1} c_{j+1}

module ADP.Fusion.Point
  ( module ADP.Fusion.Core
  , module ADP.Fusion.Point.Core
  , module ADP.Fusion.Point.SynVar.Indices
  , module ADP.Fusion.Point.SynVar.Recursive
  , module ADP.Fusion.Point.Term.Chr
  , module ADP.Fusion.Point.Term.Deletion
  , module ADP.Fusion.Point.Term.Epsilon
  , module ADP.Fusion.Point.Term.MultiChr
  , module ADP.Fusion.Point.Term.Str
  ) where

import ADP.Fusion.Core

import ADP.Fusion.Point.Core
import ADP.Fusion.Point.SynVar.Indices
import ADP.Fusion.Point.SynVar.Recursive
import ADP.Fusion.Point.Term.Chr
import ADP.Fusion.Point.Term.Deletion
import ADP.Fusion.Point.Term.Epsilon
import ADP.Fusion.Point.Term.MultiChr
import ADP.Fusion.Point.Term.Str

