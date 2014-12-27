
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | Implementation of the occasionally dishonest casino.

module Main where

import           Control.Applicative ((<$>))
import           Data.List (intersperse)
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import           Numeric.Log
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Console.CmdArgs
import           Text.Printf
import qualified System.Random.MWC.Monad as R

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion



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
  { genNumber     = 10 &= help "number of rolls"
  , switchingProb = 0.05 &= help "probability of switching"
  }

data Signature m c e x r = Signature
  { h_h :: x -> c -> x
  , h_d :: x -> c -> x
  , d_h :: x -> c -> x
  , d_d :: x -> c -> x
  , nil ::      e -> x
  , h   :: Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Signature

grammar Signature{..} c th' td' st' =
  let th = th'  ( nil <<< Empty   |||
                  h_h <<< th % c  |||
                  h_d <<< td % c  ... h
                )
      td = td'  ( d_h <<< th % c  |||
                  d_d <<< td % c  ... h
                )
      st  = st' ( id  <<< th      |||
                  id  <<< td      ... h
                )
  in Z:.th:.td:.st
{-# INLINE grammar #-}

outsideGrammar Signature{..} c th' td' st' =
  let th = th'  ( nil <<< Empty   |||
                  h_h <<< th % c  |||
                  d_h <<< td % c  ... h   -- rotated @h_d@ to @d_h@ (simpler example code)
                )
      td = td'  ( nil <<< Empty   |||
                  h_d <<< th % c  |||     -- rotation @d_h@ to @h_d@
                  d_d <<< td % c  ... h
                )
      st = st'  ( id  <<< th      ... h
                )
  in Z:.th:.td:.st

type P = Log Double -- should be log-double

forward :: Monad m => Signature m Int () P P
forward = Signature
  { h_h = \x c -> 0.95 * x * (1/6)
  , h_d = \x c -> 0.10 * x * if c==6 then (1/2) else (1/10)
  , d_h = \x c -> 0.05 * x * (1/6)
  , d_d = \x c -> 0.90 * x * if c==6 then (1/2) else (1/10)
  , nil = \()  -> 1.00
  , h = SM.foldl' (+) 0
  }
{-# INLINE forward #-}

type T = ITbl Id Unboxed PointL P
type A = IRec Id         PointL P

type Tb = ITbl Id Unboxed (Outside PointL) P
type Ab = IRec Id         (Outside PointL) P

runCasino :: [Int] -> (P,P,VU.Vector P,VU.Vector P)
runCasino is = (d,db,vh,vd) where
  i = VU.fromList is
  n = VU.length i
  !(Z:.th:.td:.st)  = mutateTablesDefault
                    $ grammar forward
                        (chr i)
                        (ITbl EmptyOk (PA.fromAssocs (pointL 0 0) (pointL 0 n) 0 []))
                        (ITbl EmptyOk (PA.fromAssocs (pointL 0 0) (pointL 0 n) 0 []))
                        (IRec EmptyOk (pointL 0 0, pointL 0 n))
      :: Z:.T:.T:.A
  d = unId $ axiom st
  !(Z:.thb:.tdb:.stb) = mutateTablesDefault
                      $ outsideGrammar forward
                          (chr i)
                          (ITbl EmptyOk (PA.fromAssocs (O $ pointL 0 0) (O $ pointL 0 n) 0 []))
                          (ITbl EmptyOk (PA.fromAssocs (O $ pointL 0 0) (O $ pointL 0 n) 0 []))
                          (IRec EmptyOk (O $ pointL 0 0, O $ pointL 0 n))
      :: Z:.Tb:.Tb:.Ab
  db = unId $ axiom stb
  vh = let ITbl _ (Unboxed _ vf) _ = th
           ITbl _ (Unboxed _ vb) _ = thb
       in  VU.zipWith (\x y -> x * y / d) vf vb
  vd = let ITbl _ (Unboxed _ vf) _ = td
           ITbl _ (Unboxed _ vb) _ = tdb
       in  VU.zipWith (\x y -> x * y / d) vf vb
{-# NOINLINE runCasino #-}

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

bla :: VU.Vector Int -> Int
bla v = unId
      . SM.foldl' (+) 0
      . staticCheck' (VU.length v > 0)
      $ let z = VU.unsafeHead v
        in  SM.enumFromStepN z 1 1
{-# NOINLINE bla #-}

takk :: VU.Vector Int -> Int
takk v = unId
       . SM.foldl' (+) 0
       . SM.take 2
       $ (SM.enumFromStepN 1 1 10) SM.++ (SM.enumFromStepN (VU.unsafeHead v) 1 1)
{-# NOINLINE takk #-}

