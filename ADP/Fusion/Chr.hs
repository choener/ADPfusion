{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
--
-- TODO PointL , PointR need sanity checks for boundaries

module ADP.Fusion.Chr where

import           Control.Exception(assert)
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU

import           Data.PrimitiveArray -- ((:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR, Outside(..))

import           ADP.Fusion.Classes
import           ADP.Fusion.Multi.Classes

import Debug.Trace



-- | A generic Character parser that reads a single character but allows
-- passing additional information.
--
--  'Chr' expects a function to retrieve @r@ at index position, followed by
--  the actual generic vector with data.

data Chr r x where
  Chr :: VG.Vector v x
      => !(v x -> Int -> r)
      -> !(v x)
      -> Chr r x

-- | smart constructor for regular 1-character parsers

chr xs = Chr VG.unsafeIndex xs
{-# INLINE chr #-}

-- | Smart constructor for Maybe Peeking, followed by a character.

chrLeft xs = Chr f xs where
  f xs k = ( xs VG.!? (k-1)
           , VG.unsafeIndex xs k
           )
  {-# INLINE [1] f #-}
{-# INLINE chrLeft #-}

instance Build (Chr r x)

instance
  ( Element ls i
  ) => Element (ls :!: Chr r x) i where
    data Elm (ls :!: Chr r x) i = ElmChr !r !i !(Elm ls i)
    type Arg (ls :!: Chr r x)   = Arg ls :. r
    getArg (ElmChr x _ ls) = getArg ls :. x
    getIdx (ElmChr _ i _ ) = i
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}



-- ** @PointL@ single-dim instances

instance
  ( Monad m
  , Element ls PointL
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Chr r x) PointL where
  mkStream (ls :!: Chr f xs) Static lu@(PointL (l:.u)) (PointL (i:.j))
    = staticCheck (j>l && j>0 && j<=u && j<= VG.length xs) $
      let !z = f xs (j-1) -- extract [j-1 , j]
      in  S.map (ElmChr z (pointL (j-1) j))
          $ mkStream ls Static lu (pointL i $ j-1)
--  mkStream _ _ _ _ = error "mkStream / Chr / PointL not implemented"
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: Chr r x) (Outside PointL) where
  mkStream (ls :!: Chr f xs) Static lu@(O (PointL (l:.u))) (O (PointL (i:.j)))
    = staticCheck (j<u) $
      let !z = f xs j
      in  S.map (ElmChr z (O . pointL j $ j+1))
          $ mkStream ls Static lu (O . pointL i $ j+1)
--  mkStream _ _ _ _ = error "mkStream / Chr / Outside PointL not implemented"
  {-# INLINE mkStream #-}



-- ** @Subword@ single-dim instances

{-
instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Chr r x) Subword where
  mkStream (ls :!: Chr f xs) Static lu@(Subword (l:.u)) ij@(Subword (i:.j))
    -- We use a static check here as we can then pull out the @z@ character
    -- lookup. In the Nussinov example (X -> f <<< z1 t z2 t) this gives
    -- a 3x performance improvement. Note that this benchmark is a bit
    -- artificial.
    --
    -- The static part is called @right-most@, i.e. when only terminals with
    -- known fixed sizes are on the right of this terminal.
    = staticCheck (j>0 && j<=u) $
      let !z = f xs (j-1)
      in S.map (ElmChr z (subword (j-1) j))
         $ mkStream ls Static lu (subword i $ j-1)
  mkStream (ls :!: Chr f xs) v lu ij@(Subword (i:.j))
    -- This version is used when to right, we already had variable-size
    -- (non-)terminals to the right.
    = S.map (\s -> let Subword (k:.l) = getIdx s
                   in  ElmChr (f xs l) (subword l $ l+1) s
            )
    $ mkStream ls v lu (subword i $ j-1)
  {-# INLINE mkStream #-}
-}

-- Note how the indices grow to the outside!

{-
instance
  ( Monad m
  , Element ls (Outside Subword)
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: Chr r x) (Outside Subword) where
  -- For the static case, we move the @j@ index.
  mkStream (ls :!: Chr f xs) Static lu@(O (Subword (l:.u))) ij@(O (Subword (i:.j)))
    = staticCheck (j>=0 && j<u) $
      let !z = f xs j
      in S.map (ElmChr z (O $ subword j (j+1)))
         $ mkStream ls Static lu (O $ subword i $ j+1)
  -- In the variable case, (i) we set @i@ to @i-1@ going further down. (ii) On
  -- going back up, we extract the rightmost index of the left symbol @l@ --
  -- which could be @i-1@ but need not be.
  mkStream (ls :!: Chr f xs) v lu ij@(O (Subword (i:.j)))
    = S.map (\s -> let O (Subword (_:.l)) = getIdx s
                   in  ElmChr (f xs l) (O . subword l $ l+1) s
            )
    $ mkStream ls v lu (O $ subword (i-1) j)
  {-# INLINE mkStream #-}
-}


-- * Multi-dimensional stuff

type instance TermArg (TermSymbol a (Chr r x)) = TermArg a :. r

{-
instance TermStaticVar (Chr r x) Subword where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (Subword (i:.j)) = subword i $ j-1
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}
-}

instance TermStaticVar (Chr r x) PointL where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (PointL (i:.j)) = pointL i $ j-1
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance TermStaticVar (Chr r x) PointR where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (PointR (i:.j)) = pointR i $ j-1
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

-- TODO removed the static check since *in principle* the statics system down
-- at the bottom of the stack should take care of it! Need to verify with
-- QuickCheck, though.

{-
instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.Subword) where
  terminalStream (a:>Chr f (!v)) (sv:.Static) (is:.Subword (i:.j))
    = id -- staticCheck (j>0)
    . S.map (\(Qd s (z:._) is e) -> Qd s z (is:.subword (j-1) j) (e:.f v (j-1)))
    . terminalStream a sv is
    . S.map (\(Tr s z (is:.i)) -> Tr s (z:.i) is)
  terminalStream (a:>Chr f (!v)) (sv:._) (is:.Subword (i:.j))
    = S.map (\(Qd s (z:.Subword (k:.l)) is e) -> Qd s z (is:.subword l (l+1)) (e:.f v (l-1)))
    . terminalStream a sv is
    . S.map (\(Tr s z (is:.i)) -> Tr s (z:.i) is)
  {-# INLINE terminalStream #-}
-}

{-
instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.PointL) where
  terminalStream (a:>Chr f (!v)) (sv:.Static) (is:.PointL (i:.j))
    = S.map (\(Qd s (z:._) is e) -> Qd s z (is:.pointL (j-1) j) (e:.f v (j-1)))
    . terminalStream a sv is
    . S.map (\(Tr s z (is:.i)) -> Tr s (z:.i) is)
  terminalStream (a:>Chr f (!v)) (sv:._) (is:.PointL (i:.j))
    = S.map (\(Qd s (z:.PointL (k:.l)) is e) -> Qd s z (is:.pointL l (l+1)) (e:.f v (l-1)))
    . terminalStream a sv is
    . S.map (\(Tr s z (is:.i)) -> Tr s (z:.i) is)
  {-# INLINE terminalStream #-}
-}

{-
instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.PointR) where
  terminalStream (a:>Chr f (!v)) (sv:.Static) (is:.PointR (i:.j))
    = S.map (\(Qd s (z:._) is e) -> Qd s z (is:.pointR (j-1) j) (e:.f v (j-1)))
    . terminalStream a sv is
    . S.map (\(Tr s z (is:.i)) -> Tr s (z:.i) is)
  terminalStream (a:>Chr f (!v)) (sv:._) (is:.PointR (i:.j))
    = S.map (\(Qd s (z:.PointR (k:.l)) is e) -> Qd s z (is:.pointR l (l+1)) (e:.f v (l-1)))
    . terminalStream a sv is
    . S.map (\(Tr s z (is:.i)) -> Tr s (z:.i) is)
  {-# INLINE terminalStream #-}
-}

