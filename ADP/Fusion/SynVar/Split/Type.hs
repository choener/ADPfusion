
{-# Language ScopedTypeVariables #-}

-- |
--
-- NOTE /highly experimental/

module ADP.Fusion.SynVar.Split.Type where

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
  data Elm     (ls :!: Split uId zOrder splitType synVar) i = ElmSplit !(Proxy uId) !(CalcSplitType splitType synVar) !i !i !(Elm ls i)
  type Arg     (ls :!: Split uId zOrder splitType synVar)   = Arg ls :. (CalcSplitType splitType synVar)
  type RecElm  (ls :!: Split uId zOrder splitType synVar) i = Elm ls i
  getArg (ElmSplit _ x _ _ ls) = getArg ls :. x
  getIdx (ElmSplit _ _ i _ _ ) = i
  getOmx (ElmSplit _ _ _ o _ ) = o
  getElm (ElmSplit _ _ _ _ ls) = ls
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
                 in  ElmSplit Proxy () (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see above) - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmSplit Proxy () kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

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
instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  , B uId (SameSid uId (Elm ls Subword)) ls Subword
  , C uId ls Subword
  , (BTy uId (SameSid uId (Elm ls Subword)) ls Subword :. Subword) ~ mix
--  , (CTy uId ls Subword :. Subword) ~ zij
--  , (PrimArrayOps arr (BuildIxTy uId ls :. Subword) x)
--  , x ~ ArgTy (Arg (ITbl m arr (BuildIxTy uId ls :. Subword) x))
--  , j ~ BuildIxTy uId (ls :!: Split uId zOrder Final (ITbl m arr j x))
  ) => MkStream m (ls :!: Split uId zOrder Final (ITbl m arr mix x)) Subword where
  mkStream (ls :!: Split (ITbl _ _ c t elm)) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                     fmbkm :: mix = ccc (Proxy :: Proxy uId) s :. subword l j
                 in  ElmSplit Proxy (t ! fmbkm) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  {-# Inline mkStream #-}



class B (uId::Symbol) (b::Bool) ls i where
  type BTy uId b ls i :: *
  bbb :: Proxy uId -> Proxy b -> Elm ls i -> BTy uId b ls i

instance B uId b S i where
  type BTy uId b S i = Z
  bbb p b (ElmS _ _) = Z

instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  , Element (ls :!: l) i
  , RecElm (ls :!: l) i ~ Elm ls i
  ) => B uId False (ls :!: l) i where
  type BTy uId False (ls :!: l) i = CTy uId ls i
  bbb p b e = ccc p (getElm e)

instance
  ( B uId (SameSid uId (Elm ls i)) ls i
  ) => B uId True  (ls :!: Split sId zOrder splitType synVar) i where
  type BTy uId True (ls :!: Split sId zOrder splitType synVar) i = CTy uId ls i :. i
  bbb p b (ElmSplit _ _ i _ e) = ccc p e :. i

type family SameSid uId elm :: Bool where
  SameSid uId (Elm (ls :!: Split sId zOrder splitType synVar) i) = uId == sId
  SameSid uId (Elm (ls :!: l                                ) i) = False

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

