
-- | The 'axiom' runs a backtracking algebra. The name comes from Robert
-- Giegerichs @ADP@ where @axiom@ runs the fully formed algorithm.

module ADPfusion.Core.SynVar.Axiom where

-- | The Axiom type class

class Axiom t where
  -- | The corresponding stream being returned by 'axiom'
  type AxiomStream t ∷ *
  -- | Index type when running the axiom
  type AxiomIx t ∷ *
  -- | Given a table, run the axiom
  axiom ∷ t → AxiomStream t
  -- | Given a table and index, run the axiom from the index on. This is useful
  -- for scanning type algorithms that need to return all locally optimal
  -- structures, as a locally optimal may start at any given index.
  axiomAt ∷ t → AxiomIx t → AxiomStream t

