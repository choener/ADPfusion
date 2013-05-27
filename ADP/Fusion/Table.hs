{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Table where

import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Data.Strict.Maybe
import Prelude hiding (Maybe(..))

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion.Classes



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

instance Build (MTbl i x)

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
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = PA.readM tbl (Z:.subword k l) >>= \z -> return $ S.Yield (ElmMTblSw s z (subword k l)) (s :!: k :!: l+1)
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
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls:!:MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) (is:.i) where
  mkStream (ls :!: MTbl enz tbl) os is
    = S.mapM (\(s:!:Z:!:β) -> PA.readM tbl β >>= \z -> return $ ElmMTbl s z β) -- extract data using β index
    . tableIndices os enz is -- generate indices for multiple dimensions
    . S.map (\s -> (s:!:Z:!:getIdx s)) -- extract the right-most current index
    $ mkStream ls os is -- TODO fix os is!
  {-# INLINE mkStream #-}

instance
  ( ValidIndex (is:.i) ls
  ) => ValidIndex (is:.i) (ls :!: MTbl (is:.i) (PA.MutArr m (arr (is:.i) x))) where



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

