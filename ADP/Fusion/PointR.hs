
-- | This exports everything needed for sequence-based alignment style
-- algorithms.
--
-- Here are some notes on implementation of the Inside and Outside 
--
-- X_j     -> S_{j-1} X_{j-1} c_j
-- Y_{j-1} -> S_?     X_j     c_j
-- Y_j     -> S_{j+1} X_{j+1} c_{j+1}

module ADP.Fusion.PointR
  ( module ADP.Fusion.Core
  , module ADP.Fusion.PointR.Core
  , module ADP.Fusion.PointR.SynVar.Indices
  , module ADP.Fusion.PointR.Term.Chr
  , module ADP.Fusion.PointR.Term.Deletion
  , module ADP.Fusion.PointR.Term.Epsilon
  , module ADP.Fusion.PointR.Term.MultiChr
  ) where

import ADP.Fusion.Core

import ADP.Fusion.PointR.Core
import ADP.Fusion.PointR.SynVar.Indices
import ADP.Fusion.PointR.Term.Chr
import ADP.Fusion.PointR.Term.Deletion
import ADP.Fusion.PointR.Term.Epsilon
import ADP.Fusion.PointR.Term.MultiChr

