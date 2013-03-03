{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module ADP.Fusion.Chr where

import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq
import qualified Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Stream.Size
import Control.Exception (assert)

import ADP.Fusion.Classes



-- | Terminal parser for a single character.

data Chr e = Chr !(VU.Vector e)



-- * Instances for dim=1.

instance MkElm x i => MkElm (x:.Chr e) i where
  newtype Plm (x:.Chr e) i = Pchr (Elm x i :. Is i :. Is i)
  newtype Elm (x:.Chr e) i = Echr (Elm x i :. Is i :. e)
  type    Arg (x:.Chr e)   = Arg x :. e
  topIdx (Echr (_:.k:._)) = k
  getArg (Echr (x:._:.t)) = getArg x :. t
  {-# INLINE topIdx #-}
  {-# INLINE getArg #-}

-- | Return a single character. If we are "outer-most" than this should be "k"
-- with "k+1==j", otherwise any "k" is ok.

instance ( Monad m, Index i, NFData (Is i), NFData e
         , Next (Chr e) i
         , MkElm ss i, MkS m ss i
         , TEE m (Chr e) i
         ) => MkS m (ss:.Chr e) i where
  mkS (ss:.ch) ox ix = S.mapM step $ mkS ss (convT ch ox) ix where
    step y = do let l = topIdx y
                let r = toR ix
                e <- tiOne ch l r
                e `deepseq` return $ Echr (y:.r:.e)
    {-# INLINE step #-}
  {-# INLINE mkS #-}

instance (Monad m, VU.Unbox e) => TEE m (Chr e) (y:.(Int:.Int)) where
  type TE (Chr e) = e
  tiOne (Chr ve) (IsIntInt (_:.l)) (IsIntInt (_:.r)) = return $ VU.unsafeIndex ve l
  te = error "not implemented"
  ti = error "not implemented"
  tisuc = error "not implemented"
  tifin = error "not implemented"
  tiget = error "not implemented"
  {-# INLINE tiOne #-}
