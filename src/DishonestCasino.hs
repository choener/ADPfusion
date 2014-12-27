
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- | Implementation of the occasionally dishonest casino.

module Main where

import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Data.Vector.Fusion.Util

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion



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

type P = Double -- should be log-double

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

runCasino :: [Int] -> (P,P,String)
runCasino is = (d,db,"") where
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
{-# NOINLINE runCasino #-}

main = runCasino []

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

