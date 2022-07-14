
-- | The functions in here auto-create suitable algebra product functions from
-- a signature. Currently, functions @<**@ are supported which have scalar
-- results in the first variable.
--
-- TODO If we want to support classified DP, we shall also need @**<@
-- generating vector-results given a vector result, followed by a scalar
-- result.
--
-- TODO Then we also need @***@ handling the case of vector-to-vector results.
--
-- TODO note the comments in @buildBacktrackingChoice@

module ADPfusion.Core.TH
  ( makeAlgebraProduct
  , (<||)
  , (**>)
  ) where

import           Data.List
import           Data.Tuple.Select
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM

import           ADPfusion.Core.TH.Backtrack -- (makeBacktrackingProductInstance,(<||))
import           ADPfusion.Core.TH.Common (getRuleResultType)



makeAlgebraProduct = makeProductInstances

{-
-- | Create the algebra product function from a signature type constructor.
--
-- TODO make the resulting function INLINE
--
-- TODO compare @synTypes@ with the stream argument types of all @hs@ (via their
-- @hns@ names). If there is a mismatch, then either not all non-terminal types
-- have a corresponding choice function or vice versa.

makeAlgebraProductH :: [Name] -> Name -> Q [Dec]
makeAlgebraProductH hns nm = do
  rnm <- reify nm
  case rnm of
    TyConI (DataD ctx tyConName args cs d) -> case cs of
      -- we analyze the accessor functions and look for the objective function
      -- accessor. It's stream parameter is the type of the non-terminal.
      -- Everything else in accessors are terminal parameters.
      [RecC dataConName fs'] -> do
        -- split @fs@ into functions applied to rule RHSs and choice functions (@hs@)
        let (fs,hs) = partition ((`notElem` hns) . sel1) fs'
        -- the result types of the @fs@ are the types of the non-terminal symbols
        let synTypes = nub . map getRuleResultType $ fs
--        funStream <- funD (mkName "<**") [genClauseStream dataConName fs' fs hs]
        funList   <- funD (mkName "<||") [genClauseBacktrack dataConName fs' fs hs]
        return
--          [ funStream
          [ funList
          , PragmaD $ InlineP (mkName "<||") Inline FunLike AllPhases
          ]
      _   -> fail "more than one data ctor"
    _          -> fail "unsupported data type"

-- | Creates a class for each type of product and instances for each
-- signature.

makeClassyProducts :: Name -> Q [Dec]
makeClassyProducts conName = do
  c <- lookupValueName "BacktrackingProduct"
  case c of
    Nothing -> error "need to create class now and add instance"
    Just cl -> error "add instance"
  return []
-}


