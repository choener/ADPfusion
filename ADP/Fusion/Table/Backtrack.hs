
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Wrap forward tables in such a way as to allow backtracking via
-- algebras.

module ADP.Fusion.Table.Backtrack where

import qualified Data.Vector.Fusion.Stream.Monadic as S

import           ADP.Fusion.Classes



-- |
--
-- TODO this should go into @ADP.Fusion.Table.Backtrack@, more than just
-- tabulated syntactic vars are going to use it.
--
-- NOTE You probably need to give the @monad morphism@ between @mF@ and
-- @mB@ so as to be able to extract forward results in the backtracking
-- phase.

class ToBT t (mF :: * -> *) (mB :: * -> *) r where
  data BT t (mF :: * -> *) (mB :: * -> *) r :: *
  type BtIx t :: *
  toBT :: t -> (forall a . mF a -> mB a) -> (BtIx t -> BtIx t -> mB (S.Stream mB r)) -> BT t mF mB r

instance Build (BT t mF mB r)

