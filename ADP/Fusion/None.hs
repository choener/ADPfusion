{-# LANGUAGE StandaloneDeriving #-}
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

instance StreamElm None i where
  newtype Elm None i = ElmNone (IxP i)
  type Arg None = Z
  getIxP (ElmNone k) = k
  getArg (ElmNone _) = Z
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

instance (NFData i, NFData (IxP i), Index i, Monad m) => MkStream m None i where
  mkStream None _ ix = let k = toL ix in (ix,k) `deepseq` S.singleton (ElmNone k)
  {-# INLINE mkStream #-}

deriving instance (Show (IxP i)) => Show (Elm None i)


-- ** NFData instances

{-
instance NFData (Elm None (Z :. (Int :. Int))) where
  rnf (Enone i) = rnf i

instance NFData (Elm None Z) where
  rnf (Enone i) = rnf i
-}

