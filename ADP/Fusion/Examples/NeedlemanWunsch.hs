{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Needleman-Wunsch global alignment algorithm. This algorithm is
-- extremely simple but provides a good showcase for what ADPfusion offers.
--
-- Follow the code from top to bottom for a tutorial on usage.
--
-- We start by importing a bunch of modules, including
-- @Data.PrimitiveArray@ for low-level arrays and automated filling of the
-- arrays or tables in the correct order.
--
-- We also need to import @ADP.Fusion@ to access the high-level code for
-- dynamic programs.
--
-- Don't forget to inline basically everything!

module Main where

import           Control.Applicative
import           Control.Monad
import           Data.Array.Repa.Index
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import qualified Control.Arrow as A
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import           System.IO.Unsafe (unsafePerformIO)
import           Control.Monad.Primitive

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion



-- | A signature connects the types of all non-terminals and terminals with
-- evaluation (or attribute) functions. In the grammar below, we not only
-- want to create all possible parses of how two strings can be aligned but
-- also evaluate each parse and choose the optimal one based on Bellman's
-- principle of optimality.
--
-- Assume we are in the matrix and want to calculate @x@:
--
-- @
--  -----
--  |d|u|
--  -----
--  |l|x|
--  -----
-- @
--
-- We can arrive from @d@, making a diagonal step, called @step_step@ as we
-- advance by one in both dimensions. This leads to an alignment of two
-- characters, one from each input, at @x@, which is combined with the
-- already calculated alignment at @d@.
--
-- We can also just step in the first dimension @step_loop@, going from @l@
-- to @x@. Which means that the first-dim character does not have
-- a partner, leading to an insert/deletion or in/del. We typically do not
-- care in which of the two dimensions the in/del happens, just that it
-- does.
--
-- The third case is an in/del in the other dimension, giving us
-- @loop_step@ or going from @u@ to @x@.
--
-- Of course, if @x@ happens to be the uppermost, leftmost cell, we have
-- nowhere to come from, so we need to inititialize (or terminate depending
-- on your view point) using the @nil_nil@ case. That one is the base case.
--
-- Now, we also want to know which of the three cases is the best case
-- (coming from @d,l,u@), this requires a "choice" function or @h@.
--
-- Now, we take a close look at the type signatures. @step_step :: x ->
-- (Z:.c:.c) -> x@ tells us that @step_step@ requires the score from the
-- non-terminal, typed @x@ for the alignment up to @d@, then we get the two
-- characters with type @c@ and produce a new non-terminal typed score @x@.
-- For our simple alignment we'll later choose @Char@ for @c@ and @Int@ for
-- @x@.
--
-- The type of @h :: Stream m x -> m r@ is more interesting. We get
-- a @Stream@ of @x@'s and produce an @r@ monadically. The left part is
-- clear @Stream m x@ are the results from the four rules, but the right
-- part allows us to maybe not only return the best case, types @x == r@,
-- but maybe the two best cases @r == (x,x)@ or similar. While we do not
-- use this feature here, it makes ADPfusion fully "classified DP"
-- capable, which is a really cool feature for advanced algorithms.

data Signature m x r c = Signature
  { step_step :: x -> (Z:.c :.c ) -> x
  , step_loop :: x -> (Z:.c :.()) -> x
  , loop_step :: x -> (Z:.():.c ) -> x
  , nil_nil   ::      (Z:.():.()) -> x
  , h         :: Stream m x -> m r
  }

-- | We also want to be able to backtrace the optimal result. Given our
-- alignment, knowing that we get an alignment score of 29 doesn't help us
-- much. But with /algebra products/ we can ask for @(optimal <** pretty)@
-- and get the optimal result /and/ the parse for it.
--
-- The @(<**)@ operator is notoriously difficult to write, so we just
-- compute it ☺.
--
-- Note that haddock actually shows @(<**)@, while you just write
-- @makeAlgebraProductH ['h] ''Signature@ (the primes are TemplateHaskell!,
-- the only TemplateHaskell we need).

makeAlgebraProductH ['h] ''Signature

-- | This is the linear grammar in two dimensions describing the
-- "Needleman-Wunsch" search space. It will, in principle, enumerate the
-- exponential number of possible alignment, but due to memoization and the
-- choice function @h@, the calculation time is @O(N^2)@ and if only one
-- optimal alignment is requested, backtracking works in linear time.
--
-- The grammar first requires a 'Signature', we use @RecordWildCards@ as
-- a language extension to bind @step_step@ and friends. We also need
-- a variable for the single non-terminal (@a@), and have two inputs @i1@
-- and @i2@. Each grammar starts with a "base case" @Z:.@ followed by one
-- or more pairs of non-terminal plus rules. Here we have one pair @(a,
-- rules)@, where in @rules@ we combine the four different rules.
--
-- @step_step \<\<\< a % (M:>chr i1:>chr i2)@, for example, means that
-- @step_step@ first gets the non-terminal @a@, which will give the score
-- up to @d@ (see the ascii-art above), followed by @(%)@ the 2-dim
-- terminal for @i1@ and @i2@.
--
-- Multi-dimensional terminals are built up from the zero-dimension @M@,
-- separated by @:>@ symbols and just bind the input. In this case we want
-- individual characters from @i1@ and @i2@, so we write @chr i1@ or @chr
-- i2@.
--
-- Different rules are combined with @(|||)@ and the optimal case is
-- selected via @...h@. Rules can, of course, be co-recursive, each rule
-- can request all terminal and non-terminal symbols.
--
-- Due to the way @nil_nil@ works on @Empty@, @nil_nil@ is actually /only/
-- called once, when we start the alignment, not for every cell!
--
-- /However/, due to this being a high-performance library, we do not
-- provide a runtime scheme to detect misbehaving rules. Some debug-code is
-- in place that performs certain checks in non-optimized GHCI sessions,
-- but optimized code is built for raw speed, without any checks.
--
-- If you are a "conventional" DP programmer, you might miss the usual
-- indices. Just as in the spiritual father of @ADPfusion@, Robert
-- Giegerichs @ADP@, we hide the actual index calculations.

grammar Signature{..} a i1 i2 =
  Z:.
  ( a, step_step <<< a % (M:>chr i1:>chr i2) |||
       step_loop <<< a % (M:>chr i1:>None  ) |||
       loop_step <<< a % (M:>None  :>chr i2) |||
       nil_nil   <<< (M:>Empty:>Empty)       ... h
  )
{-# INLINE grammar #-}

-- | A grammar alone is not enough, we also need to say what a @step_step@
-- means, or what an optimum is. Here, we do exactly that. We create an
-- instance of the 'Signature' from above. Since this is a simple example,
-- we just say that two aligned characters @a@ and @b@ yield a score of
-- @x+1@ (with @x@ the previous alignment score) if the characters are
-- identical. Otherwise we lower the score by 2. In/dels incur a cost of
-- @-1@, meaning that a mismatch is actually the same as two in/dels, one
-- in each dimension. The start of the alignment gives an initial score of
-- 0.
--
-- And the optimal choice, of course, is to start with a default of
-- @-999999@ and find the maximum of that score and the choices we are
-- given.

sScore :: Monad m => Signature m Int Int Char
sScore = Signature
  { step_step = \x (Z:.a:.b) -> if a==b then x+1 else x-2
  , step_loop = \x _         -> x-1
  , loop_step = \x _         -> x-1
  , nil_nil   = const 0
  , h = S.foldl' max (-999999)
  }
{-# INLINE sScore #-}

-- | Scores alone are not enough, we also want to pretty-print alignments.
-- An alignment are basically two strings @[String 1, String 2]@, being
-- turned into a whole stream of alignments, using @Char@s for the
-- individual characters being aligned.
--
-- We follow the same theme as in 'sScore', but this time @h = return
-- . id@, that is the choice function @h@ does not (!) make choice but
-- rather returns all alignments. You already heard about @<**@, we'll use
-- it below.

sPretty :: Monad m => Signature m [String] (S.Stream m [String]) Char
sPretty = Signature
  { step_step = \[x,y] (Z:.a :.b ) -> [a  :x, b  :y]
  , step_loop = \[x,y] (Z:.a :.()) -> [a  :x, '-':y]
  , loop_step = \[x,y] (Z:.():.b ) -> ['-':x, b  :y]
  , nil_nil   = const ["",""]
  , h = return . id
  }

-- | A single DP array or table is an unboxed table (we want performance!
-- raw blob in ram, please!) with a two-dim index @(Z:.PointL:.PointL@) and
-- @Int@ scores. @PointL@ is the index type for left-linear grammars, of
-- which we wrote one above... There are index-types for left- and
-- right-linear grammars as well as context-free grammars; and they all
-- know how to calculate themselves.

type Arr  = PA.Unboxed (Z:.PointL:.PointL) Int

-- | We have a single DP table, stacked upon @(Z:.)@. In general we have
-- @(Z:.s:.t:. ...)@ with @s@, @t@, and so on, being the non-terminal
-- memo-tables.

type Arrs = Z:.Arr

-- | Let's go and fill the tables. Given two unboxed vectors of the two
-- inputs, we want to calculate the arrays @Arrs@. First we need the
-- lengths of the two inputs.
--
-- Then we create storage for the 2-dim table with @newWithM@ and set the
-- default score to @-999999@. Then we bind the table via @mTblD@ to be
-- a multi-"D"im table. @(Z:.EmptyOk:.EmptyOk)@ allows the grammar to
-- reduce the /minimal size/ of the non-terminal to zero, i.e. @(PointL
-- k k)@.
--
-- This is important for context-free grammars where you can have
-- right-hand sides like @X -> X X@. If @X@ on the right can have a size of
-- 0, then you get infinite loops or weird (and wrong) results. By
-- disallowing empty non-terminals, all rules "shrink", which should be
-- what you want in cases like @X -> X X@.
--
-- Finally we call 'runFreezeMTbls' as @runFreezeMTbls $ grammar sScore
-- t i1 i2@ and are happy that this run function seems to know how to fill
-- the tables correctly.

forwardPhase :: (Applicative m, PrimMonad m) => VU.Vector Char -> VU.Vector Char -> m Arrs
forwardPhase i1 i2 = do
  let n1 = VU.length i1
  let n2 = VU.length i2
  !t' <- PA.newWithM (Z:.pointL 0 0:.pointL 0 0) (Z:.pointL 0 n1:.pointL 0 n2) (-999999)
  let t = mTblD (Z:.EmptyOk:.EmptyOk) t'
  runFreezeMTbls $ grammar sScore t i1 i2
{-# INLINE forwardPhase #-}

-- | Remember how we also want to know the actual alignment? The backtrack
-- function is similar to the forwardPhase where we filled the table. We
-- take the table we just filled (Z:.t') and bind @t'@ to a backtracking
-- table 'btTblD' together with a backtracking function @g@. Now we need to
-- define @g@. Well, that is simple, we just bind the grammar via
-- @(Z:.(_,g)) = grammar (sScore <** sPretty t i1 i2@ but ignore the table
-- @_@ and keep only the rules bound to @g@. Note how @g@ requires @t@
-- which in turn requires @g@ -- the joy of writing Haskell!
--
-- Finally, we call @g@ with the indices (here we still need explicit
-- indices for now!), unpack from the Id monad, unpack to a list, unpack
-- again from the Id monad, and reverse all the alignments -- as they where
-- stored back-to-front. This then gives us all the co-optimal alignments
-- which we can lazily ask for.

backtrack :: VU.Vector Char -> VU.Vector Char -> Arrs -> [[String]]
backtrack i1 i2 (Z:.t') = map (map reverse) . unId . S.toList . unId . g $ Z:.pointL 0 n1 :. pointL 0 n2 where
  n1 = VU.length i1
  n2 = VU.length i2
  t = btTblD (Z:.EmptyOk:.EmptyOk) t' g
  (Z:.(_,g)) = grammar (sScore <** sPretty) t i1 i2
{-# NOINLINE backtrack #-}

-- | Let's write Needleman-Wunsch. We give the maximal number of alignments
-- @k@ to return, and the two input sequences.
--
-- We return a pair with the optimal score and the co-optimal alignments.
--
-- Internally, we run the forward phase (in @IO@ this time, @ST s@ works
-- just as well). and calculates the backtrack result as well.
--
-- @
-- needlemanWunsch 5 "AAC" "AAD"
-- @
-- produces
-- @
-- (0,[["AAC","AAD"],["AA-C","AAD-"],["AAC-","AA-D"]])
-- @
--
-- Note that as there are exactly three co-optimal alignments of the
-- inputs, requesting five does still give only three.
--

needlemanWunsch k i1' i2' = (ws PA.! (Z:.pointL 0 n1:.pointL 0 n2), bt) where
  (Z:.ws) = unsafePerformIO (forwardPhase i1 i2)
  i1 = VU.fromList i1'
  i2 = VU.fromList i2'
  n1 = VU.length i1
  n2 = VU.length i2
  bt = take k $ backtrack i1 i2 (Z:.ws)
{-# NOINLINE needlemanWunsch #-}

-- | This wrapper takes a list of input sequences and aligns each odd
-- sequence with the next even sequence. We want one alignment for each
-- such pair.

align [] = return ()
align [c] = error "single last line"
align (a:b:xs) = do
  putStrLn a
  putStrLn b
  let (s,rs) = needlemanWunsch 1 a b 
  print s
  mapM_ (mapM_ print) rs
  align xs

-- | And finally have a minimal main that reads from stdio.
--
-- If you are brave enough then put this through @ghc-core@ and look for
-- @needlemanWunsch@ in the CORE. Everything coming from the forward phase
-- should be beautifully optimized and the algorithm should run quite fast.

main = do
  ls <- lines <$> getContents
  align ls

