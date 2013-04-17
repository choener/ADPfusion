{-# LANGUAGE PatternGuards #-}
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
--
-- TODO each combinator should come with a special outer check. Given some
-- index (say (i,j), this can then check if i-const >= 0, or j+const<=n, or
-- i+const<=j. That should speed up everything that uses GChr combinators.
-- Separating out this check means that certain inner loops can run without any
-- conditions and just jump.

module ADP.Fusion where

import Control.DeepSeq
import Data.Array.Repa.Index
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Fusion.Stream as Sp
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.Vector.Fusion.Stream.Size
import GHC.Exts (inline)
import Data.Strict.Tuple
import Data.Strict.Maybe
import Prelude hiding (Maybe(..))
import qualified Prelude as P
import Control.Monad.Primitive

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.ExtShape
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import qualified Data.Array.Repa as R

import ADP.Fusion.Apply

import Debug.Trace

-- | The Inner/Outer handler. We encode three states. We are in 'Outer' or
-- right-most position, or 'Inner' position. The 'Inner' position encodes if
-- loop conditional 'CNC' need to be performed.
--
-- In f <<< Z % table % table, the two tables already perform a conditional
-- branch, so that Z/table does not have to check boundary conditions.
--
-- In f <<< Z % table % char, no check is performed in table/char, so Z/table
-- needs to perform a boundary check.

data CNC
  = Check
  | NoCheck
  deriving (Eq,Show)

data InnerOuter
  = Inner !CNC
  | Outer
  deriving (Eq,Show)

data ENE
  = EmptyT
  | NoEmptyT
  deriving (Eq,Show)

class TransENE t where
  toEmpty :: t -> t
  toNonEmpty :: t -> t

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

chr = Chr
{-# INLINE chr #-}

instance Build (Chr x)

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
  mkStream !(ls :!: Chr xs) (Inner cnc) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmChr s (VU.unsafeIndex xs l) (subword l $ l+1)
            )
    $ mkStream ls (Inner cnc) (subword i $ j-1)
  {-# INLINE mkStream #-}

data GChr x e = GChr !(VU.Vector x)

instance Build (GChr x e)

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
  {-# INLINE gChrChk #-}
  {-# INLINE gChrGet #-}

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

-- | Currently using the 'outerCheck' function, need to test if this really works well! (benchmark!)

instance
  ( Monad m
  , VU.Unbox x
  , GChrExtract x e
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: GChr x e) Subword where
  mkStream !(ls :!: gchr) Outer !ij@(Subword(i:.j))
    = let dta = gChrGet gchr $ j-1
      in  dta `seq` S.map (\s -> ElmGChr s dta (subword (j-1) j))
--                    $ S.filter (\s -> gChrChk gchr (j-1-942))           -- NOTE the actual leq check is performed outside of the loop, but branching still occurs in the loop
                    $ outerCheck (gChrChk gchr (j-942))
                    $ mkStream ls Outer (subword i $ j-1)
  mkStream !(ls :!: gchr) (Inner cnc) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmGChr s (gChrGet gchr $ l) (subword l $ l+1))
    $ S.filter (\s -> let (Subword (k:.l)) = getIdx s
                      in  gChrChk gchr $ l)
    $ mkStream ls (Inner cnc) (subword i $ j-1)
  {-# INLINE mkStream #-}

outerCheck :: Monad m => Bool -> S.Stream m a -> S.Stream m a
outerCheck b (S.Stream step sS n) = b `seq` S.Stream snew (Left (b,sS)) Unknown where
  {-# INLINE [1] snew #-}
  snew (Left  (False,s)) = return $ S.Done
  snew (Left  (True ,s)) = return $ S.Skip (Right s)
  snew (Right s        ) = do r <- step s
                              case r of
                                S.Yield x s' -> return $ S.Yield x (Right s')
                                S.Skip    s' -> return $ S.Skip    (Right s')
                                S.Done       -> return $ S.Done
{-# INLINE outerCheck #-}

data Region x = Region !(VU.Vector x)
--              | SRegion !Int !Int !(VU.Vector x)

instance Build (Region x)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Region x) Subword where
  data Elm (ls :!: Region x) Subword = ElmRegion !(Elm ls Subword) !(VU.Vector x) !Subword
  type Arg (ls :!: Region x)         = Arg ls :. VU.Vector x
  getArg !(ElmRegion ls xs _) = getArg ls :. xs
  getIdx !(ElmRegion _ _   i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Region x) Subword where
  --
  -- 'Region's of unlimited size
  --
  mkStream !(ls:!:Region xs) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmRegion s (VU.unsafeSlice l (j-l) xs) (subword l j))
    $ mkStream ls (Inner Check) ij
  mkStream !(ls:!:Region xs) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
              in  return (s :!: l :!: l)
      step !(s :!: k :!: l)
        | l > j     =  return S.Done
        | otherwise = return $ S.Yield (ElmRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1) -- TODO the slice index positions are wrong ?!
  --
  -- Regions with size limitations
  --
  -- TODO this case seems to be rather inefficient. We should rather not do the
  -- takeWhile/dropWhile dance modify the inner index to produce only those
  -- values that are acceptable
--  mkStream !(ls:!:Region lb ub xs) Outer !ij@(Subword (i:.j))
--    = S.map       (\s -> let (Subword (k:.l)) = getIdx s in ElmRegion s (VU.unsafeSlice l (j-l) xs) (subword l j))
--    $ S.takeWhile (\s -> case mlb of Nothing -> True
--                                     Just lb -> let (Subword (k:.l)) = getIdx s in j-l >= lb)
--    $ S.dropWhile (\s -> case mub of Nothing -> False
--                                     Just ub -> let (Subword (k:.l)) = getIdx s in j-l >= ub)
--    $ mkStream ls Inner ij
{-
  -- | TODO below is wrong for sregions!
  mkStream !(ls:!:SRegion lb ub xs) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmRegion s (VU.slice l (j-l) xs) (subword l j))
    $ mkStream ls (Inner Check) ij
  mkStream !(ls:!:SRegion lb ub xs) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
              in  return (s :!: l :!: l+lb)
      step !(s :!: k :!: l) | l > j || l-k > ub
        = return S.Done
      step !(s :!: k :!: l)
        = return $ S.Yield (ElmRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1) -- TODO the slice index positions are wrong ?!
-}
  {-# INLINE mkStream #-}

region :: VU.Vector x -> Region x
region = Region
{-# INLINE region #-}

-- |
--
-- NOTE If you only want a lower bound, set the upper bound to s.th. like "1
-- Million".

--sregion :: Int -> Int -> VU.Vector x -> Region x
--sregion = SRegion
--{-# INLINE sregion #-}


instance
  (
  ) => Elms Z Subword where
  data Elm Z Subword = ElmZ !Subword
  type Arg Z = Z
  getArg !(ElmZ _) = Z
  getIdx !(ElmZ ij) = ij
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- | The bottom of every stack of RHS arguments in a grammar.

instance
  ( Monad m
  ) => MkStream m Z Subword where
  mkStream Z Outer !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k==j      = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner NoCheck) !(Subword (i:.j)) = S.singleton $ ElmZ $ subword i i
  mkStream Z (Inner Check)   !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j      = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise = P.Nothing
  {-# INLINE mkStream #-}

data Tbl x = Tbl !(PA.Unboxed (Z:.Subword) x)

instance Build (Tbl x)

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
  mkStream !(ls:!:Tbl xs) Outer !ij@(Subword (i:.j)) = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmTbl s (xs PA.! (Z:.subword l j)) (subword l j)) $ mkStream ls (Inner Check) ij
  mkStream !(ls:!:Tbl xs) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
    mk !s = let (Subword (k:.l)) = getIdx s in return (s :!: l :!: l)
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = return $ S.Yield (ElmTbl s (xs PA.! (Z:.subword k l)) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

data BtTbl m x b = BtTbl ENE !(PA.Unboxed (Z:.Subword) x) !(Subword -> m (S.Stream m b))

instance Build (BtTbl m x b)

instance TransENE (BtTbl m x b) where
  toEmpty (BtTbl _ xs f ) = BtTbl EmptyT xs f
  toNonEmpty (BtTbl _ xs f) = BtTbl NoEmptyT xs f
  {-# INLINE toEmpty #-}
  {-# INLINE toNonEmpty #-}

instance
  ( Monad m
  , Elms ls Subword
  ) => Elms (ls :!: BtTbl m x b) Subword where
  data Elm (ls :!: BtTbl m x b) Subword = ElmBtTbl !(Elm ls Subword) !x !(m (S.Stream m b)) !Subword
  type Arg (ls :!: BtTbl m x b) = Arg ls :. (x,m (S.Stream m b))
  getArg !(ElmBtTbl ls x b _) = getArg ls :. (x,b)
  getIdx !(ElmBtTbl _  _ _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: BtTbl m x b) Subword where
  mkStream !(ls:!:BtTbl ene xs f) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmBtTbl s (xs PA.! (Z:.subword l j)) (f $ subword l j) (subword l j))
    $ mkStream ls (Inner Check) (subword i $ case ene of { EmptyT -> j ; NoEmptyT -> j-1 })
  mkStream !(ls:!:BtTbl ene xs f) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
    mk !s = let (Subword (k:.l)) = getIdx s in return (s:!:l:!: case ene of {EmptyT -> l; NoEmptyT -> l+1}) -- TODO we probably want l:!:l+1
    step !(s:!:k:!:l)
      | l > j     = return $ S.Done
      | otherwise = return $ S.Yield (ElmBtTbl s (xs PA.! (Z:.subword k l)) (f $ subword k l) (subword k l)) (s:!:k:!:l+1)
  {-# INLINE mkStream #-}



data MTbl xs = MTbl ENE !xs

instance TransENE (MTbl xs) where
  toEmpty (MTbl _ xs) = MTbl EmptyT xs
  toNonEmpty (MTbl _ xs) =MTbl NoEmptyT xs
  {-# INLINE toEmpty #-}
  {-# INLINE toNonEmpty #-}

instance Build (MTbl xs)

instance
  ( Monad m
  , Elms ls Subword
  ) => Elms (ls :!: MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  data Elm (ls :!: MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword = ElmMTbl !(Elm ls Subword) !x !Subword
  type Arg (ls :!: MTbl (PA.MutArr m (arr (Z:.Subword) x))) = Arg ls :. x
  getArg !(ElmMTbl ls x _) = getArg ls :. x
  getIdx !(ElmMTbl _ _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( PrimMonad m
  , PA.MPrimArrayOps arr (Z:.Subword) x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  mkStream !(ls:!:MTbl ene tbl) Outer !ij@(Subword (i:.j))
    = S.mapM (\s -> let (Subword (_:.l)) = getIdx s in PA.readM tbl (Z:.subword l j) >>= \z -> return $ ElmMTbl s z (subword l j))
    $ mkStream ls (Inner Check) (subword i $ case ene of { EmptyT -> j ; NoEmptyT -> j-1 }) -- if nonE then (subword i $ j-1) else ij)
  mkStream !(ls:!:MTbl ene tbl) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
    mk !s = let (Subword (_:.l)) = getIdx s in return (s :!: l :!: l + case ene of { EmptyT -> 0 ; NoEmptyT -> 1 }) -- if nonE then 1 else 0)
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = PA.readM tbl (Z:.subword k l) >>= \z -> return $ S.Yield (ElmMTbl s z (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

data Empty = Empty

instance Build Empty

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Empty) Subword where
  data Elm (ls :!: Empty) Subword = ElmEmpty !(Elm ls Subword) !() !Subword
  type Arg (ls :!: Empty) = Arg ls :. ()
  getArg !(ElmEmpty ls () _) = getArg ls :. ()
  getIdx !(ElmEmpty _ _ i)   = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Empty) Subword where
  mkStream !(ls:!:Empty) Outer !ij@(Subword (i:.j))
    = S.map (\s -> ElmEmpty s () (subword i j))
    $ S.filter (\_ -> i==j)
    $ mkStream ls Outer ij
  {-# INLINE mkStream #-}





testF :: Int -> Int -> Int
testF i j =
  p7' <<< chrR testVs % chrL testVs % Tbl testA % region testVs % Tbl testA % chrR testVs % chrL testVs |||
  p7' <<< chrR testVs % chrL testVs % Tbl testA % region testVs % Tbl testA % chrR testVs % chrL testVs ... (Sp.foldl' (+) 0) $ subword i j
{-# NOINLINE testF #-}

testG :: Int -> Int -> Int
testG i j =
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs |||
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs ... (Sp.foldl' (+) 0) $ subword i j
{-# NOINLINE testG #-}

testA :: PA.Unboxed (Z:.Subword) Int
testA = PA.fromAssocs (Z:.subword 0 0) (Z:.subword 0 50) 0 []
{-# NOINLINE testA #-}

testVs :: VU.Vector Int
testVs = VU.fromList [ 0 .. 9999 ]
{-# NOINLINE testVs #-}

--gugg :: Int -> Int -> [(Int,VU.Vector Int,Int)]
gugg i j = (,,) <<< chrR testVs % region testVs % chrL testVs ... Sp.toList $ subword i j

p3 a b c = a+b+c
p4 a b c d = a+b+c+d
p5 a b c d e = a+b+c+d+e
p6 a b c d e f = a+b+c+d+e+f
p7 a b c d e f g = a+b+c+d+e+f+g
p7' (a:!:a') (b:!:b') c ds e (f:!:f') (g:!:g') = a+b+c+ VU.length ds +e+f+g + a'+b'+f'+g'
p7'' (a:!:a') (b:!:b') c d e (f:!:f') (g:!:g') = a+b+c+ d +e+f+g + a'+b'+f'+g'




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


-- | Apply a function to symbols on the RHS of a production rule. Builds the
-- stack of symbols from 'xs' using 'build', then hands this stack to
-- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- in the "outer" position. Once the stream has been created, we 'S.map'
-- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- function 'f'.

infixl 8 <<<
(<<<) f xs = S.map (apply (inline f) . getArg) . mkStream (build xs) Outer
{-# INLINE (<<<) #-}

-- | Combine two RHSs to give a choice between parses.

infixl 7 |||
(|||) xs ys = \ij -> xs ij S.++ ys ij
{-# INLINE (|||) #-}

-- | Applies the objective function 'h' to a stream 's'. The objective function
-- reduces the stream to a single optimal value (or some vector of co-optimal
-- things).

infixl 6 ...
(...) s h = h . s
{-# INLINE (...) #-}

-- | Separator between RHS symbols.

infixl 9 ~~
(~~) = (:!:)
{-# INLINE (~~) #-}

-- | This separator looks much paper "on paper" and is not widely used otherwise.

infixl 9 %
(%) = (:!:)
{-# INLINE (%) #-}

-- 
-- instance NFData Z
-- instance NFData z => NFData (z:.VU.Vector e) where
--   rnf (z:.ve) = rnf z `seq` rnf ve
-- 
-- instance NFData z => NFData (z:.Int) where
--   rnf (z:.i) = rnf z `seq` rnf i
-- 


-- | Build the stack using (%)

class Build x where
  type Stack x :: *
  type Stack x = Z :!: x
  build :: x -> Stack x
  default build :: (Stack x ~ (Z :!: x)) => x -> Stack x
  build x = Z :!: x
  {-# INLINE build #-}

instance Build x => Build (x:!:y) where
  type Stack (x:!:y) = Stack x :!: y
  build (x:!:y) = build x :!: y
  {-# INLINE build #-}

