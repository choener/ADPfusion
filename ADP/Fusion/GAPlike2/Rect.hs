
-- | Rectangular tables, non-terminals and terminals for applications on two
-- sequences, model fitting and similar strategies where you want to fit one
-- essentially linear thing to another (PSSMs and HMMs come to mind).

module ADP.Fusion.GAPlike2.Rect where

import ADP.Fusion.GAPlike2.Common



-- * New (non-) terminals

-- ** The 'Rect' ctor. We fill it with a table. All (i,j) indices are being.
-- There is not upper-triangular constraint of the i<=j. 

data Rect es = Rect !es
