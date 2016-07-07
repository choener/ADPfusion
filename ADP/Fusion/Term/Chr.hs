
module ADP.Fusion.Term.Chr
  ( module ADP.Fusion.Term.Chr.Type
  , module ADP.Fusion.Term.Chr.Point
  , module ADP.Fusion.Term.Chr.Set0
  ) where

import ADP.Fusion.Term.Chr.Point
import ADP.Fusion.Term.Chr.Set0
import ADP.Fusion.Term.Chr.Type







{-

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
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

module ADP.Fusion.Term.Chr where

import           Control.Exception(assert)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import           Data.PrimitiveArray -- ((:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR, Outside(..))


import Debug.Trace





-- ** @PointL@ single-dim instances

{-
instance
  ( Monad m
  , Element ls PointL
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Chr r x) PointL where
  mkStream (ls :!: Chr f xs) Static lu@(PointL (l:.u)) (PointL (i:.j))
    = staticCheck (j>l && j>0 && j<=u && j<= VG.length xs) $
      let !z = () -- f xs (j-1) -- let-floating leads to too early evaluation
      in  S.map (ElmChr (f xs $ j-1) (pointL (j-1) j))
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
-}


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



{-

-- * Multi-dimensional stuff

{-
instance TermStaticVar (Chr r x) Subword where
  termStaticVar   _ sv _                = sv
  termStreamIndex _ _  (Subword (i:.j)) = subword i $ j-1
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}
-}

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

-}


-}

