
-- | Nussinovs RNA secondary structure prediction algorithm via basepair
-- maximization.

module Main where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List as L
import           Data.Vector.Fusion.Util
import           Debug.Trace
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
--import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           Text.Printf

import           Data.PrimitiveArray as PA

import           ADP.Fusion



data Nussinov m x r c = Nussinov
  { unp :: x -> c -> x
  , jux :: x -> c -> x -> c -> x
  , nil :: () -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProduct ''Nussinov

{-
 - due to backtracking schemes, we need a bunch of combintors
 -
 - how to deal with sup-optimal backtracking, without having to use (*||) ?

(<||)   :: Single a -> List b   -> List b         -- co-optimal backtracking
(*||)   :: Vector a -> List b   -> List (a,b)     -- classified co-optimal backtracking
(***)   :: Single a -> Single b -> Vector (a,b)   -- classified DP

-}

bpmax :: Monad m => Nussinov m Int Int Char
bpmax = Nussinov
  { unp = \ x c     -> x
  , jux = \ x c y d -> if c `pairs` d then x + y + 1 else -999999
  , nil = \ ()      -> 0
  , h   = SM.foldl' max (-999999)
  }
{-# INLINE bpmax #-}

prob :: Monad m => Nussinov m Double Double Char
prob = Nussinov
  { unp = \ x c     -> 0.3 * x
  , jux = \ x c y d -> 0.6 * if c `pairs` d then x * y else 0
  , nil = \ ()      -> 0.1
  , h   = SM.foldl' (+) 0
  }

-- |

pairs !c !d
  =  c=='A' && d=='U'
  || c=='C' && d=='G'
  || c=='G' && d=='C'
  || c=='G' && d=='U'
  || c=='U' && d=='A'
  || c=='U' && d=='G'
{-# INLINE pairs #-}

pretty :: Monad m => Nussinov m String [String] Char -- (SM.Stream m String)
pretty = Nussinov
  { unp = \ x c     -> x ++ "."
  , jux = \ x c y d -> x ++ "(" ++ y ++ ")"
  , nil = \ ()      -> ""
  , h   = SM.toList -- return . id
  }
{-# INLINE pretty #-}

prettyL :: Monad m => Nussinov m String String Char
prettyL = Nussinov
  { unp = \ x c     -> x ++ "."
  , jux = \ x c y d -> x ++ "(" ++ y ++ ")"
  , nil = \ ()      -> ""
  , h   = SM.head -- return . id
  }
{-# INLINE prettyL #-}

grammar Nussinov{..} c t' =
  let t = t'  ( unp <<< t % c           |||
                jux <<< t % c % t % c   |||
                nil <<< Epsilon         ... h
              )
  in Z:.t
{-# INLINE grammar #-}

runNussinov :: Int -> String -> (Int,[String])
runNussinov k inp = (d, take k bs) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.t) = runInsideForward i
  d = unId $ axiom t
  bs = runInsideBacktrack i t
{-# NOINLINE runNussinov #-}

runInsideForward :: VU.Vector Char -> Z:.ITbl Id Unboxed (Subword I) Int
runInsideForward i = mutateTablesDefault
                   $ grammar bpmax
                       (chr i)
                       (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
  where n = VU.length i
{-# NoInline runInsideForward #-}

runInsideBacktrack :: VU.Vector Char -> ITbl Id Unboxed (Subword I) Int -> [String]
runInsideBacktrack i t = unId $ axiom b
  where !(Z:.b) = grammar (bpmax <|| pretty) (chr i) (toBacktrack t (undefined :: Id a -> Id a))
{-# NoInline runInsideBacktrack #-}

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runNussinov k l
    mapM_ (\x -> printf "%s %5d\n" x s) xs

