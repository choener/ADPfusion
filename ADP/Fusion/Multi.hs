{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | The multi-tape extension of ADPfusion.

module ADP.Fusion.Multi where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Classes
import ADP.Fusion.Chr (GChr (..))

-- import Data.Array.Repa.Index.Subword



{-
data Term a b where
  T    :: Term a b
  (:!) :: !(Term a b) -> !c -> Term (Term a b) c
-}

data TermBase = T

data Term a b = a :! b

instance Build (Term a b)

instance
  ( ValidIndex ls ix
  ) => ValidIndex (ls :!: Term a b) ix where
  validIndex (ls :!: t) abc ix =
    allDimensionsValid t abc ix && validIndex ls abc ix
  {-# INLINE validIndex #-}
  getParserRange (ls :!: t) ix = updateRange t ix (getParserRange ls ix)
  {-# INLINE getParserRange #-}

allDimensionsValid = undefined
updateRange = undefined

instance
  ( Elms ls ix
  ) => Elms (ls :!: Term a b) ix where
    data Elm (ls :!: Term a b) ix = ElmTerm !(Elm ls ix) !(TermOf (Term a b)) !ix
    type Arg (ls :!: Term a b) = Arg ls :. (TermOf (Term a b))
    getArg !(ElmTerm ls x _) = getArg ls :. x
    getIdx !(ElmTerm _ _ idx) = idx
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls ix
  , MkStream m ls ix
  , TermElm m (Term a b) ix
  ) => MkStream m (ls :!: Term a b) ix where
  mkStream !(ls :!: t) !io !ij
    = S.map (\(s:!:Z:!:zij:!:e) -> ElmTerm s e zij)
    $ termStream t io ij
    $ S.map (\s -> (s :!: Z :!: getIdx s))
    $ mkStream ls (leftTermIO io) (leftTermIndex ij)
  {-# INLINE mkStream #-}

leftTermIndex = id
leftTermIO = id

class
  ( Monad m
  ) => TermElm m t ix where
  type TermOf t :: *
  termStream :: t -> InOut ix -> ix -> S.Stream m (ze :!: zix :!: ix) -> S.Stream m (ze :!: zix :!: ix :!: TermOf t)

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts (GChr r xs)) (is:.Subword) where
  type TermOf (Term ts (GChr r xs)) = TermOf ts :. r
  termStream (ts :! GChr f xs) (io:.Outer) (is:.ij@(Subword(i:.j))) =
    let dta = f xs (j-1)
    in  dta `seq` S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.kl) :!: (e:.dta)))
        . termStream ts io is
        . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  termStream (ts :! GChr f xs) (io:.Inner _ _) (is:.ij)
    = S.map (\(zs :!: (zix:.kl@(Subword(k:.l))) :!: zis :!: e) -> let dta = f xs l in dta `seq` (zs :!: zix :!: (zis:.kl) :!: (e:.dta)))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  {-# INLINE termStream #-}

instance
  ( Monad m
  ) => TermElm m (TermBase) Z where
  type TermOf TermBase = Z
  termStream T _ Z = S.map (\(zs:!:zix:!:Z) -> (zs:!:zix:!:Z:!:Z))
  {-# INLINE termStream #-}

type instance ParserRange Z = Z
type instance ParserRange (tail:.head) = ParserRange tail :. ParserRange head

