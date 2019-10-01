
-- | This exports everything needed for sequence-based alignment style
-- algorithms.
--
-- Here are some notes on implementation of the Inside and Outside 
--
-- X_j     -> S_{j-1} X_{j-1} c_j
-- Y_{j-1} -> S_?     X_j     c_j
-- Y_j     -> S_{j+1} X_{j+1} c_{j+1}

module ADP.Fusion.PointL
  ( module ADP.Fusion.Core
  , module ADP.Fusion.PointL.Core
  , module ADP.Fusion.PointL.SynVar.Indices
--  , module ADP.Fusion.PointL.SynVar.Recursive
  , module ADP.Fusion.PointL.Term.Chr
  , module ADP.Fusion.PointL.Term.Deletion
  , module ADP.Fusion.PointL.Term.Epsilon
  , module ADP.Fusion.PointL.Term.MultiChr
  , module ADP.Fusion.PointL.Term.Str
  ) where

import ADP.Fusion.Core

import ADP.Fusion.PointL.Core
import ADP.Fusion.PointL.SynVar.Indices
--import ADP.Fusion.PointL.SynVar.Recursive
import ADP.Fusion.PointL.Term.Chr
import ADP.Fusion.PointL.Term.Deletion
import ADP.Fusion.PointL.Term.Epsilon
import ADP.Fusion.PointL.Term.MultiChr
import ADP.Fusion.PointL.Term.Str

