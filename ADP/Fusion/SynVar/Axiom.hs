
{-# LANGUAGE TypeFamilies #-}

-- | The 'axiom' runs a backtracking algebra. The name comes from Robert
-- Giegerichs @ADP@ where @axiom@ runs the fully formed algorithm.

module ADP.Fusion.SynVar.Axiom where

-- | The Axiom type class

class Axiom t where
  -- | The corresponding stream being returned by 'axiom'
  type AxiomStream t :: *
  -- | Given a table, run the axiom
  axiom :: t -> AxiomStream t

