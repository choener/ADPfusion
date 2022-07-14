
-- | Wrap the underlying table and the rules. Isomorphic to @(,)@.

module ADPfusion.Core.SynVar.TableWrap where



-- | Wrap tables of type @t@. The tables are strict, the functions @f@ can
-- not be strict, because we need to build grammars recursively.

data TW t f = TW !t f

instance Show t ⇒ Show (TW t f) where
  show (TW t _) = "TW(" ++ show t ++ ")"

