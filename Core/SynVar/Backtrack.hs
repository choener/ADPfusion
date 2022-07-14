
-- | Wrap forward tables in such a way as to allow backtracking via
-- algebras.

module ADPfusion.Core.SynVar.Backtrack where

import Data.Vector.Fusion.Stream.Monadic (Stream)

import ADPfusion.Core.SynVar.TableWrap



-- |
--
-- TODO this should go into @ADPfusion.Table.Backtrack@, more than just
-- tabulated syntactic vars are going to use it.
--
-- NOTE You probably need to give the @monad morphism@ between @mF@ and
-- @mB@ so as to be able to extract forward results in the backtracking
-- phase.

class GenBacktrackTable t (mF :: * -> *) (mB :: * -> *) where
  data Backtrack t (mF :: * -> *) (mB :: * -> *) :: *
  type BacktrackIndex t :: *
  toBacktrack :: t -> (forall a . mF a -> mB a) {- -> (BacktrackIndex t -> BacktrackIndex t -> mB [r]) -} -> Backtrack t mF mB

-- instance Build (TW (Backtrack t mF mB) f)

