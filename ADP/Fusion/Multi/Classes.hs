{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Multi.Classes where

import           Data.Array.Repa.Index
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.Array.Repa.Index.Points
import           Data.Array.Repa.Index.Subword

import           ADP.Fusion.Classes



-- * Multi-dimensional extension

-- | Terminates a multi-dimensional terminal symbol stack.

data M = M
  deriving (Eq,Show)

infixl 2 :>

-- | Terminal symbols are stacked together with @a@ tails and @b@ head.

data TermSymbol a b = a :> b
  deriving (Eq,Show)

-- | Extracts the type of a multi-dimensional terminal argument.

type family   TermArg x :: *
type instance TermArg M                = Z
--type instance TermArg (TermSymbol a b) = TermArg a :. b

instance (Element ls i) => Element (ls :!: TermSymbol a b) i where
  data Elm (ls :!: TermSymbol a b) i = ElmTS !(TermArg (TermSymbol a b)) !i !(Elm ls i)
  type Arg (ls :!: TermSymbol a b)   = Arg ls :. TermArg (TermSymbol a b)
  getArg (ElmTS a _ ls) = getArg ls :. a
  getIdx (ElmTS _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , MkStream m ls i
  , Element ls i
  , TerminalStream m (TermSymbol a b) i
  , TermStaticVar (TermSymbol a b) i
  ) => MkStream m (ls :!: TermSymbol a b) i where
  mkStream (ls :!: ts) sv i
    = S.map fromTerminalStream
    . terminalStream ts sv i
    . S.map toTerminalStream
    $ mkStream ls (termStaticVar ts sv i) (termStreamIndex ts sv i)
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m S is) => MkStream m S (is:.Subword) where
  mkStream S (vs:.Static) (is:.Subword (i:.j))
    = staticCheck (i==j)
    . S.map (\(ElmS z) -> ElmS (z:.subword i i))
    $ mkStream S vs is
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m S is) => MkStream m S (is:.PointL) where
  mkStream S (vs:.Static) (is:.PointL (i:.j))
    = staticCheck (i==j)
    . S.map (\(ElmS z) -> ElmS (z:.pointL i i))
    $ mkStream S vs is
  {-# INLINE mkStream #-}

instance (Monad m, MkStream m S is) => MkStream m S (is:.PointR) where
  mkStream S (vs:.Static) (is:.PointR (i:.j))
    = staticCheck (i==j)
    . S.map (\(ElmS z) -> ElmS (z:.pointR i i))
    $ mkStream S vs is
  {-# INLINE mkStream #-}

instance Monad m => MkStream m S Z where
  mkStream _ _ _ = S.singleton (ElmS Z)
  {-# INLINE mkStream #-}

-- | For multi-dimensional terminals we need to be able to calculate how the
-- static/variable signal changes and if the index for the inner part needs to
-- be modified.

class TermStaticVar t i where
  termStaticVar   :: t -> IxSV i -> i -> IxSV i
  termStreamIndex :: t -> IxSV i -> i -> i

toTerminalStream s = Tr s Z (getIdx s)
{-# INLINE toTerminalStream #-}

fromTerminalStream (Qd s Z ij e) = ElmTS e ij s
{-# INLINE fromTerminalStream #-}

data Triple a b c   = Tr !a !b !c
data Quad   a b c d = Qd !a !b !c !d

-- | Handles each individual argument within a stack of terminal symbols.

class TerminalStream m t i where
  terminalStream :: t -> IxSV i -> i -> S.Stream m (Triple s j i) -> S.Stream m (Quad s j i (TermArg t))

instance (Monad m) => TerminalStream m M Z where
  terminalStream M _ Z = S.map (\(Tr s j Z) -> Qd s j Z Z)
  {-# INLINE terminalStream #-}

instance TermStaticVar M Z where
  termStaticVar   _ _ _ = Z
  termStreamIndex _ _ _ = Z
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance
  ( TermStaticVar a is
  , TermStaticVar b i
  ) => TermStaticVar (TermSymbol a b) (is:.i) where
  termStaticVar   (a:>b) (vs:.v) (is:.i) = termStaticVar   a vs is :. termStaticVar   b v i
  termStreamIndex (a:>b) (vs:.v) (is:.i) = termStreamIndex a vs is :. termStreamIndex b v i
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance IxStaticVar Z where
  type IxSV Z = Z
  initialSV _ = Z

instance (IxStaticVar is, IxStaticVar i) => IxStaticVar (is:.i) where
  type IxSV (is:.i) = IxSV is:.IxSV i
  initialSV (is:.i) = initialSV is:.initialSV i

