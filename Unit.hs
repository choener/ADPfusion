
-- | Unit indices have just a single element in their set. This is actually
-- *not* useless, since it can be used to "fold" from another index
-- structure into the single @()@ element.

module ADPfusion.Unit
  ( module ADPfusion.Core
  , module ADPfusion.Unit.SynVar.Indices
  , module ADPfusion.Unit.Term.Deletion
  , module ADPfusion.Unit.Term.Epsilon
  ) where

import ADPfusion.Core

import ADPfusion.Unit.SynVar.Indices
import ADPfusion.Unit.Term.Deletion
import ADPfusion.Unit.Term.Epsilon

