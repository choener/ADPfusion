
-- | Wrap the underlying table and the rules. Isomorphic to @(,)@.

module ADP.Fusion.SynVar.TableWrap where



-- | Wrap tables of type @t@. The tables are strict, the functions @f@ can
-- not be strict, because we need to build grammars recursively.

--data TW t f = TW !t f

-- | Capture the combination of a memo-table with type @memoTy@.

class MkTW (monad :: * -> *) (memoTy :: *) (elemTy :: *) where
  data TW monad memoTy elemTy  :: *
  type TWTblTy monad memoTy elemTy :: *
  type TWFunTy monad memoTy elemTy :: *
  tw :: TWTblTy monad memoTy elemTy -> TWFunTy monad memoTy elemTy -> TW monad memoTy elemTy

{-
data family Hallo x :: *

newtype instance Hallo Int = HalloInt { get :: Int }
  deriving (Show)

type family Hi x :: *

type instance Hi Int = String

type instance Hi Double = String

class MkHallo x where
  mkHallo :: x -> Hallo x
  unHallo :: Hallo x -> x

instance MkHallo Int where
  mkHallo 3 = HalloInt 3
  unHallo = get
-}
