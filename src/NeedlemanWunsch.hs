{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

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
import           Control.Monad.Primitive
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import qualified Control.Arrow as A
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Printf

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

grammar Signature{..} a' i1 i2 =
  let a = a'  ( step_step <<< a % (M:>chr i1:>chr i2) |||
                step_loop <<< a % (M:>chr i1:>None  ) |||
                loop_step <<< a % (M:>None  :>chr i2) |||
                nil_nil   <<< (M:>Empty:>Empty)       ... h
              )
  in Z:.a
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
  , h = SM.foldl' max (-999999)
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

sPretty :: Monad m => Signature m [String] (SM.Stream m [String]) Char
sPretty = Signature
  { step_step = \[x,y] (Z:.a :.b ) -> [a  :x, b  :y]
  , step_loop = \[x,y] (Z:.a :.()) -> [a  :x, '-':y]
  , loop_step = \[x,y] (Z:.():.b ) -> ['-':x, b  :y]
  , nil_nil   = const ["",""]
  , h = return . id
  }

-- * This is the new way how to handle table-filling

runNeedlemanWunsch :: Int -> String -> String -> (Int,[[String]])
runNeedlemanWunsch k i1' i2' = (d, take k . S.toList . unId $ axiom b) where
  i1 = VU.fromList i1'
  i2 = VU.fromList i2'
  n1 = VU.length i1
  n2 = VU.length i2
  !(Z:.t) = mutateTablesDefault
          $ grammar sScore
              (ITbl (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.pointL 0 0:.pointL 0 0) (Z:.pointL 0 n1:.pointL 0 n2) (-999999) []))
              i1 i2
              :: Z:.ITbl Id Unboxed (Z:.PointL:.PointL) Int
  d = let (ITbl _ arr _) = t in arr PA.! (Z:.pointL 0 n1:.pointL 0 n2)
  !(Z:.b) = grammar (sScore <** sPretty) (toBT t (undefined :: Id a -> Id a)) i1 i2

-- | This wrapper takes a list of input sequences and aligns each odd
-- sequence with the next even sequence. We want one alignment for each
-- such pair.

align _ [] = return ()
align _ [c] = error "single last line"
align k (a:b:xs) = do
  putStrLn a
  putStrLn b
  let (s,rs) = runNeedlemanWunsch k a b
  forM_ rs $ \[u,l] -> printf "%s\n%s  %d\n\n" u l s
  align k xs

-- | And finally have a minimal main that reads from stdio.
--
-- If you are brave enough then put this through @ghc-core@ and look for
-- @needlemanWunsch@ in the CORE. Everything coming from the forward phase
-- should be beautifully optimized and the algorithm should run quite fast.

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  align k ls
