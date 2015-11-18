
-- |
--
-- NOTE /highly experimental/

module ADP.Fusion.SynVar.Split.Type
  ( module ADP.Fusion.SynVar.Split.Type
  , Proxy (..)
  ) where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import GHC.TypeLits
import Prelude hiding (map,mapM)
import Data.Type.Equality

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack



data SplitType = Fragment | Final

-- | The @Arg synVar@ means that we probably need to rewrite the internal
-- type resolution now!

type family CalcSplitType splitType varTy where
  CalcSplitType Fragment varTy = ()
  CalcSplitType Final    varTy = varTy

-- | Should never fail?

type family ArgTy argTy where
--  ArgTy Z = Z
  ArgTy (z:.x) = x

-- | Wraps a normal non-terminal and attaches a type-level unique identier
-- and z-ordering (with the unused @Z@ at @0@).
--
-- TODO attach empty/non-empty stuff (or get from non-splitted synvar?)
--
-- TODO re-introduce z-ordering later (once we have a sort fun)

newtype Split (uId :: Symbol) {- (zOrder :: Nat) -} (splitType :: SplitType) synVar = Split { getSplit :: synVar }

-- |
--
-- TODO Here, we probably want to default to a @NonEmpty@ condition. Or at
-- least have different versions of @split@.

split :: Proxy (uId::Symbol) -> {- Proxy (zOrder::Nat) -> -} Proxy (splitType::SplitType) -> synVar -> Split uId splitType synVar
split _ _ = Split
{-# Inline split #-}

splitNE :: (ModifyConstraint synVar) => Proxy (uId::Symbol) -> {- Proxy (zOrder::Nat) -> -} Proxy (splitType::SplitType) -> synVar -> Split uId splitType synVar
splitNE _ _ = Split . toNonEmpty
{-# Inline splitNE #-}

--type Spl uId zOrder splitType = forall synVar . Split uId zOrder splitType synVar

instance Build (Split uId splitType synVar)

instance
  ( Element ls i
  ) => Element (ls :!: Split uId splitType (ITbl m arr j x)) i where
  data Elm     (ls :!: Split uId splitType (ITbl m arr j x)) i = ElmSplitITbl !(Proxy uId) !(CalcSplitType splitType x) !i !i !(Elm ls i)
  type Arg     (ls :!: Split uId splitType (ITbl m arr j x))   = Arg ls :. (CalcSplitType splitType x)
  type RecElm  (ls :!: Split uId splitType (ITbl m arr j x)) i = Elm ls i
  getArg (ElmSplitITbl _ x _ _ ls) = getArg ls :. x
  getIdx (ElmSplitITbl _ _ i _ _ ) = i
  getOmx (ElmSplitITbl _ _ _ o _ ) = o
  getElm (ElmSplitITbl _ _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}

instance
  ( Element ls i
  ) => Element (ls :!: Split uId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i where
  data Elm     (ls :!: Split uId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i = ElmSplitBtITbl !(Proxy uId) !(CalcSplitType splitType (x, [r])) !i !i !(Elm ls i)
  type Arg     (ls :!: Split uId splitType (Backtrack (ITbl mF arr j x) mF mB r))   = Arg ls :. (CalcSplitType splitType (x,[r]))
  type RecElm  (ls :!: Split uId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i = Elm ls i
  getArg (ElmSplitBtITbl _ xs _ _ ls) = getArg ls :. xs
  getIdx (ElmSplitBtITbl _ _ i _ _ ) = i
  getOmx (ElmSplitBtITbl _ _ _ o _ ) = o
  getElm (ElmSplitBtITbl _ _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}



-- | 'collectIx' gobbles up indices that are tagged with the same symbolic
-- identifier.

collectIx
  :: forall uId ls i .
     ( SplitIxCol uId (SameSid uId (Elm ls i)) (Elm ls i)
     )
  => Proxy uId -> Elm ls i -> SplitIxTy uId (SameSid uId (Elm ls i)) (Elm ls i)
collectIx p e = splitIxCol p (Proxy :: Proxy (SameSid uId (Elm ls i))) e

-- | Closed type family that gives us a (type) function for type symbol
-- equality.

type family SameSid uId elm :: Bool where
  SameSid uId (Elm (ls :!: Split sId splitType synVar) i) = uId == sId
  SameSid uId (Elm (ls :!: TermSymbol a b            ) i) = SameSid uId (TermSymbol a b)
  SameSid uId M                                           = False
  SameSid uId (TermSymbol a (Split sId splitType synVar)) = OR (uId == sId) (SameSid uId a)
  SameSid uId (Elm (ls :!: l                         ) i) = False

-- | Type-level @(||)@

type family OR a b where
  OR False False = False
  OR a     b     = True

-- | @x ++ y@ but for inductive tuples.
--
-- TODO move to PrimitiveArray

class Zconcat x y where
  type Zpp x y :: *
  zconcat :: x -> y -> Zpp x y

instance Zconcat x Z where
  type Zpp x Z = x
  zconcat x Z = x
  {-# Inline zconcat #-}

instance 
  ( Zconcat x z
  ) => Zconcat x (z:.y) where
  type Zpp x (z:.y) = Zpp x z :. y
  zconcat x (z:.y) = zconcat x z :. y
  {-# Inline zconcat #-}

-- WORKS

-- | Actually collect split indices based on if we managed to find the
-- right @Split@ synvar (based on the right symbol).

class SplitIxCol (uId::Symbol) (b::Bool) e where
  type SplitIxTy uId b e :: *
  splitIxCol :: Proxy uId -> Proxy b -> e -> SplitIxTy uId b e



instance SplitIxCol uId b (Elm S i) where
  type SplitIxTy uId b (Elm S i) = Z
  splitIxCol p b (ElmS _ _) = Z
  {-# Inline splitIxCol #-}


instance
  ( SplitIxCol uId (SameSid uId (Elm ls i)) (Elm ls i)
  , Element (ls :!: l) i
  , RecElm (ls :!: l) i ~ Elm ls i
  ) => SplitIxCol uId False (Elm (ls :!: l) i) where
  type SplitIxTy uId False (Elm (ls :!: l) i) = SplitIxTy uId (SameSid uId (Elm ls i)) (Elm ls i)
  splitIxCol p b e = collectIx p (getElm e)
  {-# Inline splitIxCol #-}

instance
  ( SplitIxCol uId (SameSid uId (Elm ls i)) (Elm ls i)
  ) => SplitIxCol   uId True (Elm (ls :!: Split sId splitType (ITbl m arr j x)) i) where
  type SplitIxTy uId True (Elm (ls :!: Split sId splitType (ITbl m arr j x)) i) = SplitIxTy uId (SameSid uId (Elm ls i)) (Elm ls i) :. i
  splitIxCol p b (ElmSplitITbl _ _ i _ e) = collectIx p e :. i
  {-# Inline splitIxCol #-}

instance
  ( SplitIxCol uId (SameSid uId (Elm ls i)) (Elm ls i)
  ) => SplitIxCol   uId True (Elm (ls :!: Split sId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i) where
  type SplitIxTy uId True (Elm (ls :!: Split sId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i) = SplitIxTy uId (SameSid uId (Elm ls i)) (Elm ls i) :. i
  splitIxCol p b (ElmSplitBtITbl _ _ i _ e) = collectIx p e :. i
  {-# Inline splitIxCol #-}

instance
  ( SplitIxCol uId (SameSid uId (Elm ls i)) (Elm ls i)
  , Zconcat (SplitIxTy uId (SameSid uId (Elm ls i)) (Elm ls i)) (SplitIxTy uId (SameSid uId (TermSymbol a b)) (TermSymbol a b))
  ) => SplitIxCol uId True (Elm (ls :!: TermSymbol a b) i) where
  type SplitIxTy uId True (Elm (ls :!: TermSymbol a b) i) = Zpp (SplitIxTy uId (SameSid uId (Elm ls i)) (Elm ls i)) (SplitIxTy uId (SameSid uId (TermSymbol a b)) (TermSymbol a b))
  splitIxCol p b (ElmTS t i _ e) = collectIx p e `zconcat` (undefined p t :: SplitIxTy uId (SameSid uId (TermSymbol a b)) (TermSymbol a b))
  {-# Inline splitIxCol #-}

