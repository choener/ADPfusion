{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 
--
-- TODO multi-dim tables with 'OnlyZero' need a static check!

module ADP.Fusion.Table where

import           Control.Monad.Primitive
import           Data.Array.Repa.Index
import           Data.Array.Repa.Shape
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import           Data.Array.Repa.ExtShape
import           Data.Array.Repa.Index.Points
import           Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion.Classes
import ADP.Fusion.Multi.Classes



-- | A table with mutable elements and attached table constraints.

data MTbl i xs = MTbl !(TblConstraint i) !xs

mTblS :: TblConstraint i -> PA.MutArr m (arr (Z:.i) x) -> MTbl i (PA.MutArr m (arr (Z:.i) x))
mTblS = MTbl
{-# INLINE mTblS #-}

mTblD :: TblConstraint i -> PA.MutArr m (arr i x) -> MTbl i (PA.MutArr m (arr i x))
mTblD = MTbl
{-# INLINE mTblD #-}

instance Build (MTbl i x)

type MTblSubword m arr x   = MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))
type MTblMulti   m arr x i = MTbl i       (PA.MutArr m (arr i            x))

instance
  ( Element ls Subword
  ) => Element (ls :!: MTblSubword m arr x) Subword where
  data Elm (ls :!: MTblSubword m arr x) Subword = ElmMtSw !x !Subword !(Elm ls Subword)
  type Arg (ls :!: MTblSubword m arr x)         = Arg ls :. x
  getArg (ElmMtSw x _ ls) = getArg ls :. x
  getIdx (ElmMtSw x i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , Element ls Subword
  , MkStream m ls Subword
  , PA.MPrimArrayOps arr (Z:.Subword) x
  ) => MkStream m (ls :!: MTblSubword m arr x) Subword where
  mkStream (ls :!: MTbl c t) Static (Subword (i:.j))
    = S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  PA.readM t (Z:.subword l j) >>= \z -> return $ ElmMtSw z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: MTbl c t) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-minSize c)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- PA.readM t (Z:.subword k (j-z))
                             return $ S.Yield (ElmMtSw y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

-- **

instance Element ls (is:.i) => Element (ls :!: MTblMulti m arr x (is:.i)) (is:.i) where
  data Elm (ls :!: MTblMulti m arr x (is:.i)) (is:.i) = ElmMTbl !x !(is:.i) !(Elm ls (is:.i))
  type Arg (ls :!: MTblMulti m arr x (is:.i))         = Arg ls :. x
  getArg (ElmMTbl x _ ls) = getArg ls :. x
  getIdx (ElmMTbl _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , Element ls (is:.i)
  , PA.MPrimArrayOps arr (is:.i) x
  , MkStream m ls (is:.i)
  ) => MkStream m (ls :!: MTblMulti m arr x (is:.i)) (is:.i) where
  mkStream (ls :!: MTbl c t) vs is
    = S.mapM (\(Tr s _ i) -> PA.readM t i >>= \z -> return $ ElmMTbl z i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}

class TableIndices i where
  tableIndices :: (Monad m) => TblConstraint i -> IxSV i -> i -> S.Stream m (Triple z j i) -> S.Stream m (Triple z j i)

instance TableIndices Z where
  tableIndices _ _ _ = id
  {-# INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.Subword) where
  tableIndices (cs:.c) (vs:.Static) (is:.Subword (i:.j))
    = S.map (\(Tr s (x:.Subword (_:.l)) ys) -> Tr s x (is:.subword l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.Subword (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.Subword (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.subword k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}

{-

-- * Mutable table with adaptive storage.

data MTbl i xs = MTbl !(ENZ i) !xs -- (PA.MutArr m (arr i x))

mTblSw :: ENE -> PA.MutArr m (arr (Z:.Subword) x) -> MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))
mTblSw = MTbl
{-# INLINE mTblSw #-}

-- | Generate the list of indices for use in table lookup.
--
-- Don't touch stuff in greek! ζ is the interior stack of arguments, α the
-- stack of saved indices

class TableIndices i where
  tableIndices :: Monad m => InOut i -> ENZ i -> i -> S.Stream m (ζ:!:α:!:i) -> S.Stream m (ζ:!:α:!:i)



-- * Instances

instance TableIndices Z where
  tableIndices Z Z Z = id
  {-# INLINE tableIndices #-}

instance TableIndices Subword where
  -- | These actually don't make sense in 1-dim settings, we keep the code as a
  -- reminder how things should look like: @tableIndices Outer ZeroT
  -- (Subword(i:.j)) = S.map (:!:subword j j)@
  tableIndices _ ZeroT _ = error "TableIndices Subword/ZeroT does not make sense"
  tableIndices Outer _ (Subword(i:.j)) = S.map (\(ζ:!:α:!:Subword(k:.l)) -> (ζ:!:α:!:subword l j))
  tableIndices (Inner _ szd) ene (Subword(i:.j)) = S.flatten mk step Unknown where
    mk (ζ:!:α:!:kl@(Subword(k:.l))) =
      let le = l + case ene of { EmptyT -> 0 ; NonEmptyT -> 1 }
          l' = case szd of { Nothing -> le ; Just z -> max le (j-z) }
      in  return (ζ:!:α:!:l:!:l')
    step (ζ:!:α:!:k:!:l)
      | i>j = return S.Done
      | otherwise = return $ S.Yield (ζ:!:α:!:subword k l) (ζ:!:α:!:k:!:l+1)
  {-# INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.Subword) where
  tableIndices (os:.Outer) (es:._) (is:.Subword(i:.j))
    = S.map (\(ζ:!:(α:!:Subword(_:.l)):!:is) -> (ζ:!:α:!:(is:.subword l j))) -- extend index to the end
    . tableIndices os es is -- extend the @is@ part
    . S.map (\(ζ:!:α:!:(is:.i)) -> (ζ:!:(α:!:i):!:is)) -- move topmost index to α for safekeeping
  -- tables annotated with zero-width have zero width @l--l@
  -- This also reduces the number of "running indices"
  --
  -- TODO consider returning "def"ault elements here, instead of data from
  -- zero-length subword? Or does 'ZeroT' actually mean to extract (a/the)
  -- zero-length subword?
  --
  tableIndices (os:.Inner _ szd) (es:.ZeroT) (is:.Subword(i:.j))
    = S.map (\(ζ:!:(α:.Subword(k:.l)):!:is) -> (ζ:!:α:!:(is:.subword l l)))
    . tableIndices os es is
    . S.map (\(ζ:!:α:!:(is:.i)) -> (ζ:!:(α:.i):!:is))
  -- the default case, where we need to create indices
  tableIndices (os:.Inner _ szd) (es:.e) (is:.Subword(i:.j))
    = S.flatten mk step Unknown
    . tableIndices os es is
    . S.map (\(ζ:!:α:!:(is:.i)) -> (ζ:!:(α:.i):!:is))
    where mk (ζ:!:(α:.Subword (k:.l)):!:is) =
            let le = l + case e of { EmptyT -> 0 ; NonEmptyT -> 1 }
                l' = case szd of { Nothing -> le ; Just z -> max le (j-z) }
            in  return (ζ:!:α:!:is:!:l:!:l')
          step (ζ:!:α:!:is:!:k:!:l)
            | l > j = return $ S.Done
            | otherwise = return $ S.Yield (ζ:!:α:!:(is:.subword k l)) (ζ:!:α:!:is:!:k:!:l+1)
  {-#  INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.PointL) where
  tableIndices (os:.Outer) (es:._) (is:.PointL(i:.j))
    = S.map (\(ζ:!:(α:!:PointL(_:.l)):!:is) -> (ζ:!:α:!:(is:.pointL l j))) -- extend index to the end
    . tableIndices os es is -- extend the @is@ part
    . S.map (\(ζ:!:α:!:(is:.i)) -> (ζ:!:(α:!:i):!:is)) -- move topmost index to α for safekeeping
  tableIndices (os:.Inner _ szd) (es:.ZeroT) (is:.PointL(i:.j))
    = S.map (\(ζ:!:(α:.PointL(k:.l)):!:is) -> (ζ:!:α:!:(is:.pointL l l)))  -- does @l==lower bound@ have to be true here?
    . tableIndices os es is
    . S.map (\(ζ:!:α:!:(is:.i)) -> (ζ:!:(α:.i):!:is))
  -- the default case, where we need to create indices
  tableIndices (os:.Inner _ szd) (es:.e) (is:.PointL(i:.j))
    = S.flatten mk step Unknown
    . tableIndices os es is
    . S.map (\(ζ:!:α:!:(is:.i)) -> (ζ:!:(α:.i):!:is))
    where mk (ζ:!:(α:.PointL (k:.l)):!:is) =
            let le = l + case e of { EmptyT -> 0 ; NonEmptyT -> 1 }
                l' = case szd of { Nothing -> le ; Just z -> max le (j-z) }
            in  return (ζ:!:α:!:is:!:l:!:l')
          step (ζ:!:α:!:is:!:k:!:l)
            | l > j = return $ S.Done
            | otherwise = return $ S.Yield (ζ:!:α:!:(is:.pointL k l)) (ζ:!:α:!:is:!:k:!:l+1)
  {-#  INLINE tableIndices #-}

-- ** Subword

instance
  ( ValidIndex ls Subword
  , Monad m
  , PA.MPrimArrayOps arr (Z:.Subword) x
  ) => ValidIndex (ls:!:MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  validIndex (_  :!: MTbl ZeroT _) _ _ = error "table with ZeroT found, there is no reason (actually: no implementation) for 1-dim ZeroT tables"
  validIndex (ls :!: MTbl ene tbl) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    let (_,Z:.Subword (0:.n)) = PA.boundsM tbl
        minsize = max b (if ene==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: MTbl ene _) ix = let (a:!:b:!:c) = getParserRange ls ix in if ene==EmptyT then (a:!:b:!:c) else (a:!:b+1:!:c)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  data Elm (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword = ElmMTblSw !(Elm ls Subword) !x !Subword -- ElmBtTbl !(Elm ls Subword) !x !(m (S.Stream m b)) !Subword
  type Arg (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) = Arg ls :. x
  getArg !(ElmMTblSw ls x _) = getArg ls :. x
  getIdx !(ElmMTblSw _  _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , Elms ls Subword
  , MkStream m ls Subword
  , PA.MPrimArrayOps arr (Z:.Subword) x
  ) => MkStream m (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  mkStream !(ls:!:MTbl ene tbl) Outer !ij@(Subword (i:.j))
    = S.mapM (\s -> let (Subword (_:.l)) = getIdx s in PA.readM tbl (Z:.subword l j) >>= \z -> return $ ElmMTblSw s z (subword l j))
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NonEmptyT -> j-1 })
  mkStream !(ls:!:MTbl ene tbl) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (_:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NonEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in return (s :!: l :!: l')
    {-# INLINE [0] mk #-}
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = PA.readM tbl (Z:.subword k l) >>= \z -> return $ S.Yield (ElmMTblSw s z (subword k l)) (s :!: k :!: l+1)
    {-# INLINE [0] step #-}
  {-# INLINE mkStream #-}

-- ** multi-dim indices

instance
  ( Elms ls (is:.i)
  ) => Elms (ls :!: MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) (is:.i) where
  data Elm (ls :!: MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) (is:.i) = ElmMTbl !(Elm ls (is:.i)) !x !(is:.i)
  type Arg (ls :!: MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) = Arg ls :. x
  getArg !(ElmMTbl ls x _) = getArg ls :. x
  getIdx !(ElmMTbl _ _  i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , PA.MPrimArrayOps arr (is:.i) x
  , Elms ls (is:.i)
  , NonTermValidIndex (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls:!:MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) (is:.i) where
  mkStream (ls :!: MTbl enz tbl) os is
    = S.mapM (\(s:!:Z:!:β) -> PA.readM tbl β >>= \z -> return $ ElmMTbl s z β) -- extract data using β index
    . tableIndices os enz is -- generate indices for multiple dimensions
    . S.map (\s -> (s:!:Z:!:getIdx s)) -- extract the right-most current index
    $ mkStream ls (nonTermInnerOuter is os) (nonTermLeftIndex is os enz) -- TODO fix os is!
  {-# INLINE mkStream #-}

instance
  ( ValidIndex ls (is:.i)
  , PA.MPrimArrayOps arr (is:.i) x
  , NonTermValidIndex (is:.i)
  ) => ValidIndex (ls :!: MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) (is:.i) where
  validIndex (ls :!: MTbl es tbl) abc isi =
    let (_,rght) = PA.boundsM tbl
    in  nonTermValidIndex es rght abc isi && validIndex ls abc isi
  getParserRange (ls :!: MTbl es _) ix = getNonTermParserRange es ix $ getParserRange ls ix
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}

class NonTermValidIndex i where
  nonTermValidIndex :: ENZ i -> i -> ParserRange i -> i -> Bool
  getNonTermParserRange :: ENZ i -> i -> ParserRange i -> ParserRange i
  nonTermInnerOuter :: i -> InOut i -> InOut i
  nonTermLeftIndex :: i -> InOut i -> ENZ i -> i

instance NonTermValidIndex Z where
  nonTermValidIndex Z Z Z Z = True
  getNonTermParserRange Z Z Z = Z
  nonTermInnerOuter Z Z = Z
  nonTermLeftIndex Z Z Z = Z
  {-# INLINE nonTermValidIndex #-}
  {-# INLINE getNonTermParserRange #-}
  {-# INLINE nonTermInnerOuter #-}
  {-# INLINE nonTermLeftIndex #-}

instance NonTermValidIndex is => NonTermValidIndex (is:.Subword) where
  nonTermValidIndex (es:.e) (ns:.Subword(_:.n)) (abc:.(a:!:b:!:c)) (is:.Subword(i:.j)) =
    let minsize = max b (if e==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && nonTermValidIndex es ns abc is
  getNonTermParserRange (es:.e) (is:._) (abc:.(a:!:b:!:c)) =
    let b' = b + if e==EmptyT then 0 else 1
    in  getNonTermParserRange es is abc :. (a:!:b':!:c)
  nonTermInnerOuter (is:._) (os:.Outer) = nonTermInnerOuter is os :. Inner Check Nothing
  nonTermInnerOuter (is:._) (os:.Inner _ _) = nonTermInnerOuter is os :. Inner NoCheck Nothing
  nonTermLeftIndex (is:.Subword(i:.j)) (os:.o) (es:.e)
    | o==Outer && e==NonEmptyT = nonTermLeftIndex is os es :. subword i (j-1)
    | otherwise                = nonTermLeftIndex is os es :. subword i j
  {-# INLINE nonTermValidIndex #-}
  {-# INLINE getNonTermParserRange #-}
  {-# INLINE nonTermInnerOuter #-}
  {-# INLINE nonTermLeftIndex #-}

-- TODO autogenerated, check correctness

instance NonTermValidIndex is => NonTermValidIndex (is:.PointL) where
  nonTermValidIndex (es:.e) (ns:.PointL(_:.n)) (abc:.(a:!:b:!:c)) (is:.PointL(i:.j)) =
    let minsize = max b (if e==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && nonTermValidIndex es ns abc is
  getNonTermParserRange (es:.e) (is:._) (abc:.(a:!:b:!:c)) =
    let b' = b + if e==EmptyT then 0 else 1
    in  getNonTermParserRange es is abc :. (a:!:b':!:c)
  nonTermInnerOuter (is:._) (os:.Outer) = nonTermInnerOuter is os :. Inner Check Nothing
  nonTermInnerOuter (is:._) (os:.Inner _ _) = nonTermInnerOuter is os :. Inner NoCheck Nothing
  nonTermLeftIndex (is:.PointL(i:.j)) (os:.o) (es:.e)
    | o==Outer && e==NonEmptyT = nonTermLeftIndex is os es :. pointL i (j-1)
    | otherwise                = nonTermLeftIndex is os es :. pointL i j
  {-# INLINE nonTermValidIndex #-}
  {-# INLINE getNonTermParserRange #-}
  {-# INLINE nonTermInnerOuter #-}
  {-# INLINE nonTermLeftIndex #-}



data BtTbl i xs f = BtTbl !(ENZ i) !xs !f -- (i -> m (S.Stream m b))

btTbl :: ENZ i -> xs -> f -> BtTbl i xs f --(i -> m (S.Stream m b)) -> BtTbl m i xs b
btTbl = BtTbl
{-# INLINE btTbl #-}

type DefBtTbl m isi x b = BtTbl isi (PA.Unboxed isi x) (isi -> m (S.Stream m b))
type SwBtTbl m x b = BtTbl Subword (PA.Unboxed (Z:.Subword) x) (Subword -> m (S.Stream m b))

instance Build (BtTbl i xs f)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: SwBtTbl m x b) Subword where
  data Elm (ls :!: SwBtTbl m x b) Subword = ElmSwBtTbl !(Elm ls Subword) !(x,m (S.Stream m b)) !Subword
  type Arg (ls :!: SwBtTbl m x b) = Arg ls :. (x,m (S.Stream m b))
  getArg !(ElmSwBtTbl ls x _) = getArg ls :. x
  getIdx !(ElmSwBtTbl _ _  i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls Subword
  , VU.Unbox x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: SwBtTbl m x b) Subword where
  mkStream !(ls:!:BtTbl ene tbl f) Outer !ij@(Subword (i:.j))
    = S.mapM (\s -> let (Subword (_:.l)) = getIdx s in return $ ElmSwBtTbl s (tbl PA.! (Z:.subword l j), f $ subword l j) (subword l j))
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NonEmptyT -> j-1 })
  mkStream !(ls:!:BtTbl ene tbl f) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (_:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NonEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in return (s :!: l :!: l')
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = return $ S.Yield (ElmSwBtTbl s (tbl PA.! (Z:.subword k l), f $ subword k l) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

instance
  ( ValidIndex ls Subword
  , VU.Unbox x
  ) => ValidIndex (ls :!: SwBtTbl m x b) Subword where
  validIndex (_  :!: BtTbl ZeroT _ _) _ _ = error "table with ZeroT found, there is no reason (actually: no implementation) for 1-dim ZeroT tables"
  validIndex (ls :!: BtTbl ene tbl _) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    let (_,Z:.Subword (0:.n)) = PA.bounds tbl
        minsize = max b (if ene==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: BtTbl ene _ f) ix = let (a:!:b:!:c) = getParserRange ls ix in if ene==EmptyT then (a:!:b:!:c) else (a:!:b+1:!:c)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls (is:.i)
  ) => Elms (ls :!: DefBtTbl m (is:.i) x b) (is:.i) where
  data Elm (ls :!: DefBtTbl m (is:.i) x b) (is:.i) = ElmBtTbl !(Elm ls (is:.i)) !(x,m (S.Stream m b)) !(is:.i)
  type Arg (ls :!: DefBtTbl m (is:.i) x b) = Arg ls :. (x,m (S.Stream m b))
  getArg !(ElmBtTbl ls x _) = getArg ls :. x
  getIdx !(ElmBtTbl _ _  i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls (is:.i)
  , ExtShape (is:.i)
  , Shape (is:.i)
  , VU.Unbox x
  , NonTermValidIndex (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls:!:DefBtTbl m (is:.i) x b) (is:.i) where
  mkStream (ls :!: BtTbl enz tbl f) os is
    = S.map (\(s:!:Z:!:β) -> ElmBtTbl s (tbl PA.! β,f β) β) -- extract data using β index
    . tableIndices os enz is -- generate indices for multiple dimensions
    . S.map (\s -> (s:!:Z:!:getIdx s)) -- extract the right-most current index
    $ mkStream ls (nonTermInnerOuter is os) (nonTermLeftIndex is os enz) -- TODO fix os is!
  {-# INLINE mkStream #-}

instance
  ( ValidIndex ls (is:.i)
  , Shape (is:.i)
  , ExtShape (is:.i)
  , VU.Unbox x
  , NonTermValidIndex (is:.i)
  ) => ValidIndex (ls :!: DefBtTbl m (is:.i) x b) (is:.i) where
  validIndex (ls :!: BtTbl es tbl f) abc isi =
    let (_,rght) = PA.bounds tbl
    in  nonTermValidIndex es rght abc isi && validIndex ls abc isi
  getParserRange (ls :!: BtTbl es _ _) ix = getNonTermParserRange es ix $ getParserRange ls ix
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}



class EmptyTable x where
  toEmptyT :: x -> x
  toNonEmptyT :: x -> x

instance (EmptyENZ (ENZ i)) => EmptyTable (MTbl i xs) where
  toEmptyT    (MTbl enz xs) = MTbl (toEmptyENZ    enz) xs
  toNonEmptyT (MTbl enz xs) = MTbl (toNonEmptyENZ enz) xs
  {-# INLINE toEmptyT #-}
  {-# INLINE toNonEmptyT #-}

instance (EmptyENZ (ENZ i)) => EmptyTable (BtTbl i xs f) where
  toEmptyT    (BtTbl enz xs f) = BtTbl (toEmptyENZ    enz) xs f
  toNonEmptyT (BtTbl enz xs f) = BtTbl (toNonEmptyENZ enz) xs f
  {-# INLINE toEmptyT #-}
  {-# INLINE toNonEmptyT #-}




{-

-- * Backtracking tables.

data BtTbl m x b = BtTbl ENE !(PA.Unboxed (Z:.Subword) x) !(Subword -> m (S.Stream m b))

instance Build (BtTbl m x b)

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
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NoEmptyT -> j-1 })
  mkStream !(ls:!:BtTbl ene xs f) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (k:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NoEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in  return (s:!:l:!: l')
    step !(s:!:k:!:l)
      | l > j     = return $ S.Done
      | otherwise = return $ S.Yield (ElmBtTbl s (xs PA.! (Z:.subword k l)) (f $ subword k l) (subword k l)) (s:!:k:!:l+1)
  {-# INLINE mkStream #-}



-- * Unboxed mutable table for the forward phase in one dimension.

data MTbl xs = MTbl !ENE !xs

instance
  ( ValidIndex ls Subword
  , Monad m
  , PA.MPrimArrayOps arr (Z:.Subword) x
  ) => ValidIndex (ls:!:MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  validIndex (_  :!: MTbl ZeroT _) _ _ = error "table with ZeroT found, there is no reason (actually: no implementation) for 1-dim ZeroT tables"
  validIndex (ls :!: MTbl ene tbl) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    let (_,Z:.Subword (0:.n)) = PA.boundsM tbl
        minsize = max b (if ene==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: MTbl ene _) ix = let (a:!:b:!:c) = getParserRange ls ix in if ene==EmptyT then (a:!:b:!:c) else (a:!:b+1:!:c)
  {-# INLINE getParserRange #-}

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
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NoEmptyT -> j-1 })
  mkStream !(ls:!:MTbl ene tbl) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (_:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NoEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in return (s :!: l :!: l')
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = PA.readM tbl (Z:.subword k l) >>= \z -> return $ S.Yield (ElmMTbl s z (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}



{-

-- ** multi-tape generalization: empty / nonempty

instance
  ( ValidIndex ls (is:.i)
  , Monad m
  , PA.MPrimArrayOps arr (is:.i) x
  ) => ValidIndex (ls :!: MTbl (PA.MutArr m (arr (is:.i) x))) (is:.i) where
    validIndex (ls :!: MTbl ene tbl) (is:.i) =
      let
      in  undefined

instance
  ( Monad m
  ) => Elms (ls :!: MTbl (PA.MutArr m (arr (is:.i) x))) (is:.i) where

instance
  ( Monad m
  ) => MkStream m (ls:!: MTbl (PA.MutArr m (arr (is:.i) x))) (is:.i) where
  mkStream !(ls:!:MTbl ene tbl) io is
    = undefined



{-
data GMtbl i x = forall m . GMtbl (ENEdim i) (PA.MutArr m (Storage i x))

-}

-}

-}


{-

-- * Immutable tables.

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
  mkStream !(ls:!:Tbl xs) Outer !ij@(Subword (i:.j)) = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmTbl s (xs PA.! (Z:.subword l j)) (subword l j)) $ mkStream ls (Inner Check Nothing) ij
  mkStream !(ls:!:Tbl xs) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (k:.l)) = getIdx s
                le = l -- TODO need to add ENE here ! -- + case ene of { EmptyT -> 0 ; NoEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in  return (s :!: l :!: l')
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = return $ S.Yield (ElmTbl s (xs PA.! (Z:.subword k l)) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}


-}


-}

