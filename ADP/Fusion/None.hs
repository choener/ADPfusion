{-# LANGUAGE UndecidableInstances #-}
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

instance
  ( NFData (IxP i)
  ) => StreamElm None i where
  newtype Elm None i = ElmNone (IxP i)
  type Arg None = Z
  getIxP (ElmNone k) = k
  getArg (ElmNone i) = i `deepseq` Z
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

instance (NFData i, NFData (IxP i), NFData (IxT i), Index i, Monad m) => MkStream m None i where
  mkStream None ox ix = let k = toL ix in (ox,ix,k) `deepseq` S.singleton (ElmNone k)
  {-# INLINE mkStream #-}

instance (NFData (IxP i)) => NFData (Elm None i) where
  rnf (ElmNone i) = rnf i

instance NFData None where
  rnf None = ()

deriving instance (Show (IxP i)) => Show (Elm None i)


-- ** NFData instances

{-
instance NFData (Elm None (Z :. (Int :. Int))) where
  rnf (Enone i) = rnf i

instance NFData (Elm None Z) where
  rnf (Enone i) = rnf i
-}

