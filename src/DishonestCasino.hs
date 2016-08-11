
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | Implementation of the occasionally dishonest casino from @Biological
-- Sequence Analysis, Durbin et al@. This code shows how a direct low-level
-- implementation of a forward-backward algorithm looks like in
-- @ADPfusion@.

module Main where

import           Control.Applicative ((<$>))
import           Data.List (intersperse)
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import           Numeric.Log
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import qualified System.Random.MWC.Monad as R
import           System.Console.CmdArgs
import           Text.Printf

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion.Point



-- | The signature. The functions @h_h, h_d, d_h, d_d@ encode transition
-- between honest and dishonest states, as well as emission. @nil@ is
-- called in case of the initial state. @h@ the choice function.

data Signature m c e x r = Signature
  { h_h :: x -> c -> x
  , h_d :: x -> c -> x
  , d_h :: x -> c -> x
  , d_d :: x -> c -> x
  , idd :: x      -> x
  , nil ::      e -> x
  , h   :: Stream m x -> m r
  }

-- Generating an algebra product is not required here, as we want to use
-- the internal data structures, not backtrack on these. We generate one
-- anyway, in case someone wants to write a viterbi algebra and
-- pretty-printing.

makeAlgebraProductH ['h] ''Signature

-- | The forward grammar. @st@ encodes the start non-terminal which collect
-- from both, the honest and dishonest case. We use @idd == id@ since we
-- don't plan on doing anything with the candidates here.

forwardGrammar Signature{..} c th' td' st' =
  let th = th'  ( nil <<< Epsilon |||
                  h_h <<< th % c  |||
                  h_d <<< td % c  ... h
                )
      td = td'  ( d_h <<< th % c  |||
                  d_d <<< td % c  ... h
                )
      st  = st' ( idd <<< th      |||
                  idd <<< td      ... h
                )
  in Z:.th:.td:.st
{-# INLINE forwardGrammar #-}

-- | The backward gramma. We simplify a bit and switch the tagged functions
-- around, saving us from having to write explicit backward algebras.
-- Having different implementations is not always a requirement, but often
-- with backward algebras. The types of the individual functions stay the
-- same, however. Typically the backward algebras will be somewhat like
-- mirroring functions to the forward ones.

backwardGrammar Signature{..} (!c) th' td' st' = Z:.th:.td:.st
  where
  th = th'  ( nil <<< Epsilon |||
              h_h <<< th % c  |||
              d_h <<< td % c  ... h   -- rotated @h_d@ to @d_h@ (simpler example code)
            )
  td = td'  ( nil <<< Epsilon |||
              h_d <<< th % c  |||     -- rotation @d_h@ to @h_d@
              d_d <<< td % c  ... h
            )
  st = st'  ( idd <<< th      ... h
            )
{-# INLINE backwardGrammar #-}

-- | Calculations in probability space are prone to finite-math errors. We
-- use log-space operations from @log-domain@ to keep numeric errors in
-- check.

type P = Log Double -- should be log-double

-- | Very simple algebra. If we are "honest", we roll normal dice, if we
-- are dishonest we roll with loaded dice. The assumed values are as in
-- Chp.3 of Bio Sequence Analysis.

forward :: Monad m => Signature m Int () P P
forward = Signature
  { h_h = \x c -> 0.95 * x * (1/6)
  , h_d = \x c -> 0.10 * x * if c==6 then (1/2) else (1/10)
  , d_h = \x c -> 0.05 * x * (1/6)
  , d_d = \x c -> 0.90 * x * if c==6 then (1/2) else (1/10)
  , idd = \x   -> x
  , nil = \()  -> 1.00
  , h = SM.foldl' (+) 0
  }
{-# INLINE forward #-}

type T = ITbl Id Unboxed PointL P
type A = IRec Id         PointL P

type Tb = ITbl Id Unboxed (Outside PointL) P
type Ab = IRec Id         (Outside PointL) P

-- | Enter list of die rolls, return the forward and backward totals (@Z@)
-- and the log-prob vectors for the honest and dishonest cases. For each
-- column @exp h + exp d == 1@ should hold, given that we have
-- log-probabilities.
--
-- TODO We currently handle calculating the probability vectors manually
-- (using @x * y / Z@). We should add facilities for these calculations to
-- one of our libraries.

runCasino :: [Int] -> (P,P,VU.Vector P,VU.Vector P)
runCasino is = (d,db,vh,vd) where
  i = VU.fromList is
  n = VU.length i
  (Z:.th:.td:.st) = runForward n i
  d = unId $ axiom st
  (Z:.thb:.tdb:.stb) = runBackward n i
  db = unId $ axiom stb
  vh = let ITbl _ (Unboxed _ _ vf) _ = th
           ITbl _ (Unboxed _ _ vb) _ = thb
       in  VU.zipWith (\x y -> x * y / d) vf vb
  vd = let ITbl _ (Unboxed _ _ vf) _ = td
           ITbl _ (Unboxed _ _ vb) _ = tdb
       in  VU.zipWith (\x y -> x * y / d) vf vb
{-# NOINLINE runCasino #-}

-- | Extracted functionality to run the forward algorithm

runForward :: Int -> VU.Vector Int -> (Z:.T:.T:.A)
runForward (!n) (!i)
  = {-# SCC "runForward" #-} mutateTablesDefault
  $ forwardGrammar forward
      (chr i)
      (ITbl EmptyOk (PA.fromAssocs (pointL 0 0) (pointL 0 n) 0 []))
      (ITbl EmptyOk (PA.fromAssocs (pointL 0 0) (pointL 0 n) 0 []))
      (IRec EmptyOk (pointL 0 0) (pointL 0 n))
{-# NOINLINE runForward #-}

-- | Same for the backward algorithm.

runBackward :: Int -> VU.Vector Int -> (Z:.Tb:.Tb:.Ab)
runBackward (!n) (!i)
  = {-# SCC "runBackward" #-} mutateTablesDefault
  $ backwardGrammar forward
      (chr i)
      (ITbl EmptyOk (PA.fromAssocs (O $ pointL 0 0) (O $ pointL 0 n) 0 []))
      (ITbl EmptyOk (PA.fromAssocs (O $ pointL 0 0) (O $ pointL 0 n) 0 []))
      (IRec EmptyOk (O $ pointL 0 0) (O $ pointL 0 n))
{-# NOINLINE runBackward #-}



-- * Machinery for generating example data, and running the algorithm.

-- | Either run the casino program, reading data from stdin, or generate
-- data. @DishonestCasino gen | DishonestCasino casino@ should produce an
-- example.

data Options
  = Casino
    { width :: Int
    }
  | Gen
    { genNumber :: Int
    , switchingProb :: Double
    }
  deriving (Show,Data,Typeable)

oCasino = Casino
  { width = 1 &= help "width"
  }

oGen = Gen
  { genNumber     = 24 &= help "number of rolls"
  , switchingProb = 0.05 &= help "probability of switching"
  }

-- | Pretty-print results.

prettyCasino :: Int -> [Char] -> [Int] -> String
prettyCasino w xs' is' = printf "%12.6f %12.6f\n\n" (ln df) (ln db) ++ go (' ':xs') (0:is') phs
  where (df,db,vh',_) = runCasino is'
        phs = map (exp . ln) . VU.toList $ vh'
        go [] _ _ = ""
        go xs is ps = (concat . intersperse " " . map (printf "%5c")   $ take k xs) ++ "\n" ++
                      (concat . intersperse " " . map (printf "%5d")   $ take k is) ++ "\n" ++
                      (concat . intersperse " " . map (printf "%5.3f") $ take k ps) ++ "\n" ++
                      go (drop k xs) (drop k is) (drop k ps)
        k = 25

main = do
  o <- cmdArgs $ modes [oCasino,oGen]
  case o of
    Gen n p -> do
      rs <- R.runWithSystemRandom . R.asRandIO $ generate True n p
      mapM_ (printf "%c") $ map fst rs
      putStrLn ""
      mapM_ (printf "%d") $ map snd rs
      putStrLn ""
    Casino w -> do
      xs <- getLine
      rs <- (map (read . (:[]))) <$> getLine
      putStrLn $ prettyCasino w xs rs

-- | Simple random data generator.

generate :: Bool -> Int -> Double -> R.Rand IO [(Char,Int)]
generate b n p
  | n==0 = return []
  | b    = do r  <- R.uniformR (1,6)
              h  <- R.uniformR (1,20 :: Int)
              rs <- generate (h<20) (n-1) p
              return $ ('H',r) : rs
  | otherwise = do r  <- clamp <$> R.uniformR (1,11)
                   h  <- R.uniformR (1,20 :: Int)
                   rs <- generate (h<3) (n-1) p
                   return $ ('D',r) : rs
  where clamp x = if x>6 then 6 else x



-- * Test functions for static check and outward floating lets.

bla :: VU.Vector Int -> Int
bla v = unId
      . SM.foldl' (+) 0
      . staticCheck (VU.length v > 0)
      $ let z = VU.unsafeHead v
        in  SM.enumFromStepN z 1 1
{-# NOINLINE bla #-}

takk :: VU.Vector Int -> Int
takk v = unId
       . SM.foldl' (+) 0
       . SM.take 2
       $ (SM.enumFromStepN 1 1 10) SM.++ (SM.enumFromStepN (VU.unsafeHead v) 1 1)
{-# NOINLINE takk #-}

