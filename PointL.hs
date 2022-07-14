
-- | This exports everything needed for sequence-based alignment style
-- algorithms.
--
-- Here are some notes on implementation of the Inside and Outside 
--
-- X_j     -> S_{j-1} X_{j-1} c_j
-- Y_{j-1} -> S_?     X_j     c_j
-- Y_j     -> S_{j+1} X_{j+1} c_{j+1}

module ADPfusion.PointL
  ( module ADPfusion.Core
  , module ADPfusion.PointL.Core
  , module ADPfusion.PointL.SynVar
  , module ADPfusion.PointL.SynVar.Indices
--  , module ADPfusion.PointL.SynVar.Recursive
  , module ADPfusion.PointL.Term.Chr
  , module ADPfusion.PointL.Term.Deletion
  , module ADPfusion.PointL.Term.Epsilon
  , module ADPfusion.PointL.Term.MultiChr
  , module ADPfusion.PointL.Term.PeekIndex
  , module ADPfusion.PointL.Term.Str
  , module ADPfusion.PointL.Term.Switch
  ) where

import ADPfusion.Core

import ADPfusion.PointL.Core
import ADPfusion.PointL.SynVar
import ADPfusion.PointL.SynVar.Indices
--import ADPfusion.PointL.SynVar.Recursive
import ADPfusion.PointL.Term.Chr
import ADPfusion.PointL.Term.Deletion
import ADPfusion.PointL.Term.Epsilon
import ADPfusion.PointL.Term.MultiChr
import ADPfusion.PointL.Term.PeekIndex
import ADPfusion.PointL.Term.Str
import ADPfusion.PointL.Term.Switch

