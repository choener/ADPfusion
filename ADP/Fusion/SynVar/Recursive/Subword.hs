
module ADP.Fusion.SynVar.Recursive.Subword where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Recursive.Type
import ADP.Fusion.SynVar.Backtrack
