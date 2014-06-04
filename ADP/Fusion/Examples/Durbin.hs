{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Nussinovs RNA secondary structure prediction algorithm via basepair
-- maximization. Follow this file from top to bottom for a short tutorial
-- on how to use @ADPfusion@.
--
-- In general the task is the following: We are given a sequence of
-- characters from the alphabet @ACGU@. There are 6 pairing rules (cf.
-- 'pairs'), @A-U@, @C-G@, @G-C@, @G-U@, @U-A@, and @U-G@ can /pair/ with
-- each other. Pairs, denoted by brackets @(@, @)@ may be juxtaposed
-- @().()@ or enclosing @(())@. /Crossing/ pairs are not allowed: @([)]@ is
-- forbidden, with @()@ and @[]@ pairing. Dots @.@ denote unpaired
-- characters.
--
-- As an example, the sequence @CACAAGGAUU@ admits the following
-- dot-bracket string @(.)..((..))@.
--
-- The algorithm below maximizes the number of legal brackets.

module Main where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Array.Repa.Index
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Text.Printf

-- Import PrimitiveArray for low-level tables and automatic table
-- filling.

import           Data.PrimitiveArray as PA

-- High-level ADPfusion stuff.

import           ADP.Fusion



-- | All grammars require a signature.

data Durbin m c e x r = Durbin
  { nil :: e           -> x
  , lef :: c -> x      -> x
  , rig :: x -> c      -> x
  , pai :: c -> x -> c -> x
  , spl :: x -> x      -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Durbin

bpmax :: Monad m => Durbin m Char () Int Int
bpmax = Durbin
  { nil = \ ()    -> 0
  , lef = \ _  x  -> x
  , rig = \ x  _  -> x
  , pai = \ c x d -> if pairs c d then x+1 else -999999
  , spl = \ x y   -> x+y
  , h   = SM.foldl' max 0
  }
{-# INLINE bpmax #-}

pairs !c !d
  =  c=='A' && d=='U'
  || c=='C' && d=='G'
  || c=='G' && d=='C'
  || c=='G' && d=='U'
  || c=='U' && d=='A'
  || c=='U' && d=='G'
{-# INLINE pairs #-}

pretty :: Monad m => Durbin m Char () String (SM.Stream m String)
pretty = Durbin
  { nil = \ ()      -> ""
  , lef = \ _  x    -> "." ++ x
  , rig = \ x  _    -> x ++ "."
  , pai = \ _  x  _ -> "(" ++ x ++ ")"
  , spl = \ x  y    -> x ++ y
  , h   = return . id
  }
{-# INLINE pretty #-}

-- grammar :: Durbin m Char () x r -> c' -> t' -> (t', Subword -> m r)
grammar Durbin{..} c t =
  Z:.
  (t, nil <<< Empty           |||
      lef <<< c  % t          |||
      rig <<< t  % c          |||
      pai <<< c  % t  % c     |||
      spl <<< t' % t'         ... h
  ) where t' = toNonEmpty t
{-# INLINE grammar #-}

forward :: VU.Vector Char -> ST s (Z:.Unboxed Subword Int)
forward inp = do
  let n  = VU.length inp
  let c  = chr inp
  !t' <- PA.newWithM (subword 0 0) (subword 0 n) (-999999)
  let t  = mTblS EmptyOk t'
  -- fillTable $ grammar bpmax c t
  -- PA.freeze t'
  runFreezeMTbls $ grammar bpmax c t
{-# NOINLINE forward #-}

fillTable (MTbl _ t,f) = do
  let (_,Subword (_:.n)) = boundsM t
  forM_ [n,n-1 .. 0] $ \i -> forM_ [i..n] $ \j ->
    (f $ subword i j) >>= PA.writeM t (subword i j)
{-# INLINE fillTable #-}

backtrack :: VU.Vector Char -> Z :. PA.Unboxed Subword Int -> [String]
backtrack inp (Z:.t') = unId . SM.toList . unId . g $ subword 0 n where
  n = VU.length inp
  c = chr inp
  t = btTblS EmptyOk t' g
  (Z:.(_,g)) = grammar (bpmax <** pretty) c t
{-# NOINLINE backtrack #-}

runDurbin :: Int -> String -> (Int,[String])
runDurbin k inp = (t PA.! (subword 0 n), take k b) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  (Z:.t) = runST $ forward i
  b = backtrack i (Z:.t)
{-# NOINLINE runDurbin #-}

main = do
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (k,[x]) = runDurbin 1 l
    printf "%s %5d\n" x k

