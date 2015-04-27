
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Wrap forward tables in such a way as to allow backtracking via
-- algebras.

module ADP.Fusion.SynVar.Backtrack where

import Data.Vector.Fusion.Stream.Monadic (Stream)

import ADP.Fusion.Base



-- |
--
-- TODO this should go into @ADP.Fusion.Table.Backtrack@, more than just
-- tabulated syntactic vars are going to use it.
--
-- NOTE You probably need to give the @monad morphism@ between @mF@ and
-- @mB@ so as to be able to extract forward results in the backtracking
-- phase.

class GenBacktrackTable t (mF :: * -> *) (mB :: * -> *) r where
  data Backtrack t (mF :: * -> *) (mB :: * -> *) r :: *
  type BacktrackIndex t :: *
  toBacktrack :: t -> (forall a . mF a -> mB a) -> (BacktrackIndex t -> BacktrackIndex t -> mB [r]) -> Backtrack t mF mB r

instance Build (Backtrack t mF mB r)

