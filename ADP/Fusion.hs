{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

-- | Generalized fusion system for grammars.
--
-- NOTE Symbols typically do not check bound data for consistency. If you, say,
-- bind a terminal symbol to an input of length 0 and then run your grammar,
-- you probably get errors, garbled data or random crashes. Such checks are
-- done via asserts in non-production code.

module ADP.Fusion where

import Control.DeepSeq
import Data.Array.Repa.Index
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Fusion.Stream as Sp
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.Vector.Fusion.Stream.Size
import GHC.Exts (inline)

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.ExtShape
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import qualified Data.Array.Repa as R

import ADP.Fusion.Apply

import Debug.Trace

data InnerOuter
  = Inner
  | Outer
  deriving (Eq,Show)

infixl 3 :!:
data a :!: b = !a :!: !b

class Elms x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i

class Index i where
  type InOut i :: *

{-
instance Index (Int:!:Int) where
  type InOut (Int:!:Int) = InnerOuter
-}

instance Index Subword where
  type InOut Subword = InnerOuter

instance Index (is:.i) where
  type InOut (is:.i) = InOut is :. InnerOuter

class (Monad m) => MkStream m x i where
  mkStream :: x -> InOut i -> i -> S.Stream m (Elm x i)

data Chr x = Chr !(VU.Vector x)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Chr x) Subword where
  data Elm (ls :!: Chr x) Subword = ElmChr !(Elm ls Subword) !x !Subword
  type Arg (ls :!: Chr x) = Arg ls :. x
  getArg !(ElmChr ls x _) = getArg ls :. x
  getIdx !(ElmChr _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- |
--
-- For 'Outer' cases, we extract the data, 'seq' it and then stream. This moves
-- extraction out of the loop.

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Chr x) Subword where
  mkStream !(ls :!: Chr xs) Outer !ij@(Subword(i:.j)) =
    let dta = VU.unsafeIndex xs (j-1)
    in  dta `seq` S.map (\s -> ElmChr s dta (subword (j-1) j)) $ mkStream ls Outer (subword i $ j-1)
  mkStream !(ls :!: Chr xs) Inner !ij@(Subword(i:.j)) =
    S.map (\s -> let (Subword (k:.l)) = getIdx s
                 in  ElmChr s (VU.unsafeIndex xs l) (subword l j)
          ) $ mkStream ls Inner (subword i $ j-1)
  {-# INLINE mkStream #-}

data GChr x e = GChr !(VU.Vector x)

class GChrExtract x e where
  type GChrRet x e :: *
  gChrChk :: GChr x e -> Int -> Bool
  gChrGet :: GChr x e -> Int -> GChrRet x e

data GChrDef

instance (VUM.Unbox x) => GChrExtract x GChrDef where
  type GChrRet x GChrDef = x
  gChrChk _ !k = True
  gChrGet !(GChr xs) !k = VU.unsafeIndex xs k
  {-# INLINE gChrChk #-}
  {-# INLINE gChrGet #-}

gchr :: VU.Unbox e => VU.Vector e -> GChr e GChrDef
gchr !xs = GChr xs
{-# INLINE gchr #-}

data PeekL

instance (VUM.Unbox x) => GChrExtract x PeekL where
  type GChrRet x PeekL = (x :!: x)
  gChrChk _ !k = k>0
  gChrGet !(GChr xs) !k = (VU.unsafeIndex xs (k-1) :!: VU.unsafeIndex xs k)
  {-# INLINE gChrChk #-}
  {-# INLINE gChrGet #-}

chrL :: VU.Unbox e => VU.Vector e -> GChr e PeekL
chrL !xs = GChr xs
{-# INLINE chrL #-}

data PeekR

instance (VUM.Unbox x) => GChrExtract x PeekR where
  type GChrRet x PeekR = (x:!:x)
  gChrChk !(GChr xs) !k = k+1 < VU.length xs
  gChrGet !(GChr xs) !k = (VU.unsafeIndex xs k :!: VU.unsafeIndex xs (k+1))

chrR :: VU.Unbox e => VU.Vector e -> GChr e PeekR
chrR !xs = GChr xs
{-# INLINE chrR #-}



instance
  ( Elms ls Subword
  ) => Elms (ls :!: GChr e r) Subword where
  data Elm (ls :!: GChr e r) Subword = ElmGChr !(Elm ls Subword) !(GChrRet e r) !Subword
  type Arg (ls :!: GChr e r) = Arg ls :. (GChrRet e r)
  getArg !(ElmGChr ls x _) = getArg ls :. x
  getIdx !(ElmGChr _ _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , GChrExtract x e
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: GChr x e) Subword where
  mkStream !(ls :!: gchr) Outer !ij@(Subword(i:.j))
    | gChrChk gchr (j-1) = let dta = gChrGet gchr $ j-1
                           in  dta `seq` S.map (\s -> ElmGChr s dta (subword (j-1) j)) $ mkStream ls Outer (subword i $ j-1)
    | otherwise = S.empty
  mkStream !(ls :!: gchr) Inner !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmGChr s (gChrGet gchr $ l) (subword l j))
    $ S.filter (\s -> let (Subword (k:.l)) = getIdx s
                      in  gChrChk gchr $ l)
    $ mkStream ls Inner (subword i $ j-1)
  {-# INLINE mkStream #-}





instance
  (
  ) => Elms Z Subword where
  data Elm Z Subword = ElmZ !Subword
  type Arg Z = Z
  getArg !(ElmZ _) = Z
  getIdx !(ElmZ ij) = ij
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  ) => MkStream m Z Subword where
  mkStream Z Outer !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k==j      = Just $ (ElmZ (subword i i), j+1)
      | otherwise = Nothing
  mkStream Z Inner !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j      = Just $ (ElmZ (subword i i), j+1)
      | otherwise = Nothing
  {-# INLINE mkStream #-}

data Tbl x = Tbl !(PA.Unboxed (Z:.Subword) x)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Tbl x) Subword where
  data Elm (ls :!: Tbl x) Subword = ElmTbl !(Elm ls Subword) !x !Subword
  type Arg (ls :!: Tbl x) = Arg ls :. x
  getArg !(ElmTbl ls x _) = getArg ls :. x
  getIdx !(ElmTbl _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Tbl x) Subword where
  mkStream (ls:!:Tbl xs) Outer ij@(Subword (i:.j)) = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmTbl s (xs PA.! (Z:.subword l j)) (subword l j)) $ mkStream ls Inner ij
  mkStream (ls:!:Tbl xs) Inner ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls Inner ij where
    mk !s = let (Subword (k:.l)) = getIdx s in return (s :!: l)
    step !(s :!: k)
      | k > j = return S.Done
      | otherwise = return $ S.Yield (ElmTbl s (xs PA.! (Z:.subword k j)) (subword k j)) (s :!: k+1)
  {-# INLINE mkStream #-}

testF :: Int -> Int -> Int
testF i j = Sp.foldl' (+) 0 $ S.map (apply (p7') . getArg) $ mkStream (Z :!: chrR testVs :!: chrL testVs :!: Tbl testA :!: Tbl testA :!: Tbl testA :!: chrR testVs :!: chrL testVs) Outer (Subword (i:.j))
{-# NOINLINE testF #-}

testA :: PA.Unboxed (Z:.Subword) Int -- R.Array R.U R.DIM2 Int
testA = PA.fromAssocs (Z:.subword 0 0) (Z:.subword 0 50) 0 []  -- R.fromUnboxed (R.ix2 100 100) testVs
{-# NOINLINE testA #-}

testVs :: VU.Vector Int
testVs = VU.fromList [ 0 .. 9999 ]
{-# NOINLINE testVs #-}

p3 a b c = a+b+c
p4 a b c d = a+b+c+d
p5 a b c d e = a+b+c+d+e
p6 a b c d e f = a+b+c+d+e+f
p7 a b c d e f g = a+b+c+d+e+f+g
p7' (a:!:a') (b:!:b') c d e (f:!:f') (g:!:g') = a+b+c+d+e+f+g + a'+b'+f'+g'

-- multi-tape version

{-
data Term ts = Term !ts

data T = T

class TermIdx ix where
  allOuter :: ix -> InOut ix -> Bool
  anyOuter :: ix -> InOut ix -> Bool

instance TermIdx Z where
  allOuter Z _ = True
  anyOuter Z _ = True
  {-# INLINE allOuter #-}
  {-# INLINE anyOuter #-}

instance (TermIdx is) => TermIdx (is:.i) where
  allOuter (is:._) (os:.o) = case o of
    Inner -> False
    Outer -> allOuter is os
  anyOuter (is:._) (os:.o) = case o of
    Outer -> True
    Inner -> anyOuter is os
  {-# INLINE allOuter #-}
  {-# INLINE anyOuter #-}

class TermElms ts ix where
  data TermElm ts ix :: *
--  data MaybeTermElm ts ix :: *
  preAllTerm :: ts -> ix -> TermElm ts ix
  preAnyTerm :: ts -> ix -> TermElm ts ix

class TermIoIdx ts ix where
  termIO :: ts -> InOut ix -> ix -> InOut ix
  termIX :: ts -> InOut ix -> ix -> ix

instance
  ( Monad m
  , TermIdx ix
  , TermElms ts ix
  , TermIoIdx ts ix
  , MkStream m ls ix
  ) => MkStream m (ls:!:Term ts) ix where
  mkStream (ls:!:Term ts) io ix
    | allOuter ix io = let pre = preAllTerm ts ix
                           f p = return undefined
                       in pre `seq` S.mapM (f pre) $ mkStream ls (termIO ts io ix) (termIX ts io ix)
    | anyOuter ix io = let pre = preAnyTerm ts ix
                           f p = return undefined
                           mk  = undefined
                           step = undefined
                       in pre `seq` S.mapM (f pre) $ S.flatten mk step Unknown $ mkStream ls (termIO ts io ix) (termIX ts io ix)
    | otherwise      = let mk = undefined
                           step = undefined
                       in S.flatten mk step Unknown $ mkStream ls (termIO ts io ix) (termIX ts io ix)
  {-# INLINE mkStream #-}

testMT :: Int -> Int -> Int
testMT i j = Sp.foldl' (+) 0
           $ S.map (apply mtp3 . getArg)
           $ mkStream (Z :!: Term (T:.Chr testVs:.Chr testVs) :!: Tbl4 testAA :!: Term (T:.Chr testVs:.Chr testVs))
                      (Z:.Outer:.Outer)
                      (Z:.(i:!:j):!:(i:!:j))

data Tbl4 x = Tbl4 !(R.Array R.U DIM4 x)

testAA :: R.Array R.U DIM4 Int
testAA = R.fromUnboxed (R.ix4 20 20 20 20) (VU.fromList [ 0 .. 20^4 ])
{-# NOINLINE testAA #-}

mtp3 (T:.a:.b) k (T:.c:.d) = a+b + k + c+d
-}

-- type level reverse

class Rev l r where
  type R l r :: *
  rev :: l -> r -> R l r

instance Rev Z r where
  type R Z r = r
  rev Z r = r

instance (Rev ts (rs:.h)) => Rev (ts:.h) rs where
  type R (ts:.h) rs = R ts (rs:.h)
  rev (ts:.h) rs = rev ts (rs:.h)


-- -- | Apply a function to symbols on the RHS of a production rule. Builds the
-- -- stack of symbols from 'xs' using 'build', then hands this stack to
-- -- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- -- in the "outer" position. Once the stream has been created, we 'S.map'
-- -- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- -- function 'f'.
-- 
-- infixl 8 <<<
-- (<<<) f xs = S.map (apply f . getArg) . mkStream (build xs) initT
-- {-# INLINE (<<<) #-}
-- 
-- -- | Combine two RHSs to give a choice between parses.
-- 
-- infixl 7 |||
-- (|||) xs ys = \ij -> xs ij S.++ ys ij
-- {-# INLINE (|||) #-}
-- 
-- -- | Applies the objective function 'h' to a stream 's'. The objective function
-- -- reduces the stream to a single optimal value (or some vector of co-optimal
-- -- things).
-- 
-- infixl 6 ...
-- (...) s h = h . s
-- {-# INLINE (...) #-}
-- 
-- -- | Separator between RHS symbols.
-- 
-- infixl 9 ~~
-- (~~) = (:.)
-- {-# INLINE (~~) #-}
-- 
-- -- | This separator looks much paper "on paper" and is not widely used otherwise.
-- 
-- infixl 9 %
-- (%) = (:.)
-- {-# INLINE (%) #-}
-- 
-- 
-- instance NFData Z
-- instance NFData z => NFData (z:.VU.Vector e) where
--   rnf (z:.ve) = rnf z `seq` rnf ve
-- 
-- instance NFData z => NFData (z:.Int) where
--   rnf (z:.i) = rnf z `seq` rnf i
-- 
