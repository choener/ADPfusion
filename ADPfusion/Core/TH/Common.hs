
module ADPfusion.Core.TH.Common where

import           Data.Tuple.Select
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax



-- | The last @Name@ of a rule is the name of the syntactic type of the
-- result.

getRuleResultType :: VarStrictType -> Name
getRuleResultType vst = go $ sel3 vst where
  go t
    | AppT _ (VarT x) <- t = x
    | AppT _ x        <- t = go x
    | otherwise            = error $ "undetermined error:" ++ show vst

