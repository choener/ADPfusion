
-- | This exports everything needed for sequence-based alignment style
-- algorithms.
--
-- Here are some notes on implementation of the Inside and Outside 
--
-- X_j     -> S_{j-1} X_{j-1} c_j
-- Y_{j-1} -> S_?     X_j     c_j
-- Y_j     -> S_{j+1} X_{j+1} c_{j+1}

module ADPfusion.PointR
  ( module ADPfusion.Core
  , module ADPfusion.PointR.Core
  , module ADPfusion.PointR.SynVar.Indices
  , module ADPfusion.PointR.Term.Chr
  , module ADPfusion.PointR.Term.Deletion
  , module ADPfusion.PointR.Term.Epsilon
  , module ADPfusion.PointR.Term.MultiChr
  ) where

import ADPfusion.Core

import ADPfusion.PointR.Core
import ADPfusion.PointR.SynVar.Indices
import ADPfusion.PointR.Term.Chr
import ADPfusion.PointR.Term.Deletion
import ADPfusion.PointR.Term.Epsilon
import ADPfusion.PointR.Term.MultiChr

