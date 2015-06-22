
-- |
--
-- NOTE /highly experimental/

module ADP.Fusion.SynVar.Split.Type where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import GHC.TypeLits
import Prelude hiding (map,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base

import ADP.Fusion.SynVar.Array.Type -- TODO temporary



data SplitType = Fragment | Final

-- | The @Arg synVar@ means that we probably need to rewrite the internal
-- type resolution now!

type family CalcSplitType splitType synVar where
  CalcSplitType Fragment synVar = ()
  CalcSplitType Final    synVar = ArgTy (Arg synVar)  -- TODO for now ... 

-- | Should never fail?

type family ArgTy argTy where
--  ArgTy Z = Z
  ArgTy (z:.x) = x

-- | Wraps a normal non-terminal and attaches a type-level unique identier
-- and z-ordering (with the unused @Z@ at @0@).
--
-- TODO attach empty/non-empty stuff (or get from non-splitted synvar?)

newtype Split (uId :: Symbol) (zOrder :: Nat) (splitType :: SplitType) synVar = Split { getSplit :: synVar }

instance
  ( Element ls i
  ) => Element (ls :!: Split uId zOrder splitType synVar) i where
  data Elm     (ls :!: Split uId zOrder splitType synVar) i = ElmSplit !(CalcSplitType splitType synVar) !i !i !(Elm ls i)
  type Arg     (ls :!: Split uId zOrder splitType synVar)   = Arg ls :. (CalcSplitType splitType synVar)
  type RecElm  (ls :!: Split uId zOrder splitType synVar) i = Elm ls i
  getArg (ElmSplit x _ _ ls) = getArg ls :. x
  getIdx (ElmSplit _ i _ _ ) = i
  getOmx (ElmSplit _ _ o _ ) = o
  getElm (ElmSplit _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}



instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Split uId zOrder Fragment synVar) Subword where
  mkStream (ls :!: Split _) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                 in  ElmSplit () (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see above) - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmSplit () kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

class GetIxTy x where
  type IxTy x :: *

instance GetIxTy (ITbl m arr i x) where
  type IxTy (ITbl m arr i x) = i

type family Natty z where
  Natty Z = 0
  Natty (z:.x) = Natty z + 1

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Split uId zOrder Final synVar) Subword where
  mkStream (ls :!: Split synVar) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                 in  ElmSplit undefined (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  {-# Inline mkStream #-}

