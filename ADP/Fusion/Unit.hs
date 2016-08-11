
-- | Unit indices have just a single element in their set. This is actually
-- *not* useless, since it can be used to "fold" from another index
-- structure into the single @()@ element.

module ADP.Fusion.Unit
  ( module ADP.Fusion.Core
  , module ADP.Fusion.Term.Deletion.Unit
  , module ADP.Fusion.SynVar.Indices.Unit
  , module ADP.Fusion.Term.Epsilon.Unit
  ) where

import ADP.Fusion.Core

import ADP.Fusion.Term.Deletion.Unit
import ADP.Fusion.Term.Epsilon.Unit
import ADP.Fusion.SynVar.Indices.Unit

