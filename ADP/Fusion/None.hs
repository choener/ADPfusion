{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module ADP.Fusion.None where

import Data.Array.Repa.Index
import Control.DeepSeq
import qualified Data.Vector.Fusion.Stream.Monadic as S

import ADP.Fusion.Classes



data None = None

instance MkElm None i where
  newtype Plm None i = Pnone (Is i)
  newtype Elm None i = Enone (Is i)
  type Arg None = Z
  topIdx (Enone k) = k
  getArg (Enone _) = Z
  {-# INLINE topIdx #-}
  {-# INLINE getArg #-}

instance (NFData i, NFData (Is i), Index i, Monad m) => MkS m None i where
  mkS None _ idx = let k = toL idx in (idx,k) `deepseq` S.singleton (Enone k)
  {-# INLINE mkS #-}



-- ** NFData instances

instance NFData (Elm None (Z :. (Int :. Int))) where
  rnf (Enone i) = rnf i

instance NFData (Elm None Z) where
  rnf (Enone i) = rnf i

