
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
import Data.Vector.Fusion.Stream.Size
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

split :: Proxy (uId::Symbol) -> {- Proxy (zOrder::Nat) -> -} Proxy (splitType::SplitType) -> synVar -> Split uId splitType synVar
split _ _ = Split
{-# Inline split #-}

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



{-
type family BuildIxTy (uId :: Symbol) ls where
  BuildIxTy uId S = Z
  BuildIxTy uId (ls :!: Split sId zOrder splitType synVar) = BuildIxTyHelper uId (ls :!: Split sId zOrder splitType synVar) (uId == sId)
  BuildIxTy uId (ls :!: other) = BuildIxTy uId ls

type family BuildIxTyHelper (uId :: Symbol) ls (sameId :: Bool) where
  BuildIxTyHelper uId (ls :!: Split uId zOrder splitType synVar) True  = BuildIxTy uId ls :. Subword
  BuildIxTyHelper uId (ls :!: Split uId zOrder splitType synVar) False = BuildIxTy uId ls

class Get (uId :: Symbol) ls i where
  get :: Proxy uId -> Elm ls i -> BuildIxTy uId ls

instance Get uId S i where
  get _ (ElmS _ _) = Z

instance
  ( sameId ~ (uId==sId)
  , GetHelper uId sameId (ls :!: Split sId zOrder splitType synVar) i
  ) => Get uId (ls :!: Split sId zOrder splitType synVar) i where
  get p = getHelper p (Proxy :: Proxy sameId)

class GetHelper (uId :: Symbol) (sameId :: Bool) ls i where
  getHelper :: Proxy uId -> Proxy Bool -> Elm ls i -> BuildIxTy uId ls

instance GetHelper uId True (ls :!: Split sId zOrder splitType synVar) i where
  getHelper p sp = undefined

-}


class B (uId::Symbol) (b::Bool) ls i where
  type BTy uId b ls i :: *
  bbb :: Proxy uId -> Proxy b -> Elm ls i -> BTy uId b ls i

instance B uId b S i where
  type BTy uId b S i = Z
  bbb p b (ElmS _ _) = Z
  {-# Inline bbb #-}

instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  , Element (ls :!: l) i
  , RecElm (ls :!: l) i ~ Elm ls i
  ) => B uId False (ls :!: l) i where
  type BTy uId False (ls :!: l) i = CTy uId ls i
  bbb p b e = ccc p (getElm e)
  {-# Inline bbb #-}

-- TODO ?
{-
instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  ) => B uId False  (ls :!: Split sId zOrder splitType  (ITbl m arr j x)) i where
  type BTy uId False (ls :!: Split sId zOrder splitType (ITbl m arr j x)) i = CTy uId ls i
  bbb p b (ElmSplitITbl _ _ i _ e) = ccc p e
  {-# Inline bbb #-}
-}

instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  ) => B   uId True (ls :!: Split sId splitType (ITbl m arr j x)) i where
  type BTy uId True (ls :!: Split sId splitType (ITbl m arr j x)) i = CTy uId ls i :. i
  bbb p b (ElmSplitITbl _ _ i _ e) = ccc p e :. i
  {-# Inline bbb #-}

instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  ) => B   uId True (ls :!: Split sId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i where
  type BTy uId True (ls :!: Split sId splitType (Backtrack (ITbl mF arr j x) mF mB r)) i = CTy uId ls i :. i
  bbb p b (ElmSplitBtITbl _ _ i _ e) = ccc p e :. i
  {-# Inline bbb #-}

type family SameSid uId elm :: Bool where
  SameSid uId (Elm (ls :!: Split sId splitType synVar) i) = uId == sId
  SameSid uId (Elm (ls :!: l                         ) i) = False

class C (uId::Symbol) ls i where
  type CTy uId ls i :: *
  cCC :: Proxy uId -> Proxy (SameSid uId (Elm ls i)) -> Elm ls i -> CTy uId ls i
  ccc :: Proxy uId ->                                   Elm ls i -> CTy uId ls i

instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  ) => C uId ls i where
  type CTy uId ls i = BTy uId (SameSid uId (Elm ls i)) ls i
  cCC p b e = bbb p b     e
  ccc p   e = cCC p Proxy e
  {-# Inline cCC #-}
  {-# Inline ccc #-}



{-

class Y (x :: Bool) where
  y :: (Proxy x) -> String

instance Y True where
  y Proxy = "True"

instance Y False where
  y Proxy = "False"

class Equal x y where
  equal' :: x -> y -> (Proxy (x==y)) -> String
  equal  :: x -> y                   -> String

instance
  ( Y (x==y)
  ) => Equal x y where
  equal' _ _ p = y p
  equal  x y   = equal' x y Proxy

-}

