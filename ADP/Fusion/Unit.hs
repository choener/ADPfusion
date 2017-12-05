
-- | Unit indices have just a single element in their set. This is actually
-- *not* useless, since it can be used to "fold" from another index
-- structure into the single @()@ element.

module ADP.Fusion.Unit
  ( module ADP.Fusion.Core
  , module ADP.Fusion.Unit.SynVar.Indices
  , module ADP.Fusion.Unit.Term.Deletion
  , module ADP.Fusion.Unit.Term.Epsilon
  ) where

import ADP.Fusion.Core

import ADP.Fusion.Unit.SynVar.Indices
import ADP.Fusion.Unit.Term.Deletion
import ADP.Fusion.Unit.Term.Epsilon

