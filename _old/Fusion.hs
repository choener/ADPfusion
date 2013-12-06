{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Pure combinators along the lines of original ADP. We simply re-export the
-- monadic interface without the monadic function application combinator.

module ADP.Fusion
  ( module ADP.Fusion.Monadic
  , module ADP.Fusion.Monadic.Internal
  ) where

import ADP.Fusion.Monadic hiding ((#<<))
import ADP.Fusion.Monadic.Internal (Scalar(..))
