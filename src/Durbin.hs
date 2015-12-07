
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
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
--import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           Text.Printf
import           Data.Char (ord)

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

makeAlgebraProduct ''Durbin

bpmax :: Monad m => Durbin m Char () Int Int
bpmax = Durbin
  { nil = \ ()    -> 0
  , lef = \ _  x  -> x
  , rig = \ x  _  -> x
  , pai = \ c x d -> x + pairs' c d -- if pairs c d then x+1 else -999999
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

pairs' !c !d = lkup_pairs ! (Z:.ord c:.ord d)
{-# Inline pairs' #-}

lkup_pairs :: Unboxed (Z:.Int:.Int) Int
lkup_pairs = PA.fromAssocs (Z:.0:.0) (Z:.mx:.mx) (-999999) $ Prelude.map (\[p1,p2] -> ((Z:.p1:.p2),1)) ps
  where mx = maximum $ Prelude.map ord "ACGU"
        ps :: [[Int]]
        ps = Prelude.map (Prelude.map ord) [ "AU", "CG", "GC", "GU", "UA", "UG" ]
{-# NoInline lkup_pairs #-}

pretty :: Monad m => Durbin m Char () String [String]
pretty = Durbin
  { nil = \ ()      -> ""
  , lef = \ _  x    -> "." ++ x
  , rig = \ x  _    -> x ++ "."
  , pai = \ _  x  _ -> "(" ++ x ++ ")"
  , spl = \ x  y    -> x ++ y
  , h   = SM.toList
  }
{-# INLINE pretty #-}

-- grammar :: Durbin m Char () x r -> c' -> t' -> (t', Subword -> m r)
grammar Durbin{..} c t' =
  let t = t'  ( nil <<< Epsilon     |||
                lef <<< c  % t      |||
                rig <<< t  % c      |||
                pai <<< c  % t  % c |||
                spl <<< tt % tt     ... h
              )
      tt = toNonEmpty t
      {-# Inline tt #-}
  in (Z:.t)
{-# INLINE grammar #-}

runDurbin :: Int -> String -> (Int,[String])
runDurbin k inp = (d, [""]) where -- take k . unId $ axiom b) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.t) = mutateTablesDefault
          $ grammar bpmax
              (chr i)
              (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) [])) :: Z:.ITbl Id Unboxed EmptyOk (Subword I) Int
  -- d = let (ITbl _ _ arr _) = t in arr PA.! subword 0 n
  d = iTblArray t PA.! subword 0 n
  -- !(Z:.b) = grammar (bpmax <|| pretty) (chr i) (toBacktrack t (undefined :: Id a -> Id a))
{-# NoInline runDurbin #-}

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runDurbin k l
    mapM_ (\x -> printf "%s %5d\n" x s) xs

