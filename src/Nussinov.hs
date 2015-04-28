
{-# LANGUAGE BangPatterns #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

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
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           Text.Printf

import           Data.PrimitiveArray as PA

import           ADP.Fusion



data Nussinov m c x r = Nussinov
  { unp :: x -> c -> x
  , jux :: x -> c -> x -> c -> x
  , nil :: () -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Nussinov

{- The code below is mainly to see how one could write the algebra product manually
 -
(<<*) f s = Nussinov unp jux nil h where
  Nussinov unpF juxF nilF hF = f
  Nussinov unpS juxS nilS hS = s
  --unp (x,xs) c          = (unpF x c    , xs >>= \xs' -> return $ SM.concatMap (\x -> SM.singleton $ unpS x c) xs')
  unp (x,xs) c          = (unpF x c    , xs >>= return . SM.concatMap (\x -> SM.singleton $ unpS x c))
  --jux (x,xs) c (y,ys) d = (juxF x c y d, xs >>= \xs' -> ys >>= \ys' -> return $ SM.concatMap (\x -> SM.concatMap (\y -> SM.singleton $ juxS x c y d) ys') xs')
  jux (x,xs) c (y,ys) d = (juxF x c y d, xs >>= return . SM.concatMapM (\x -> ys >>= return . SM.concatMapM (\y -> return . SM.singleton $ juxS x c y d)))
  nil e                 = (nilF e      , return $ SM.singleton (nilS e))
  h xs = do
    hfs <- hF $ SM.map fst xs
    let phfs = SM.concatMapM snd . SM.filter ((hfs==) . fst) $ xs
    hS phfs
-}
{-
(<||) f s = Nussinov unp jux nil h where
  Nussinov unpF juxF nilF hF = f
  Nussinov unpS juxS nilS hS = s
  unp (x,xs) c          = (unpF x c    , [unpS x c     | x <- xs])
  jux (x,xs) c (y,ys) d = (juxF x c y d, [juxS x c y d | x <- xs, y <- ys])
  nil e                 = (nilF e      , [nilS e])
  h xs = do
    ys <- SM.toList xs
    --hfs <- hF $ SM.map fst xs
    hfs <- hF $ SM.map fst $ SM.fromList ys
    --hfs <- hF $ SM.map fst $ SM.fromList ys
    --tmp1 <- SM.toList $ SM.map snd $ SM.filter ((hfs==) . fst) $ xs
    --let tmp1 = L.map snd $ L.filter ((hfs==) . fst) ys
    -- _ $ hS $ SM.fromList $ SM.concatMap snd $ SM.filter ((hfs==) . fst) $ xs
    hS $ SM.concatMap (SM.fromList . snd) $ SM.filter ((hfs==) . fst) $ SM.fromList $ ys
-}
{-# Inline (<||) #-}

{-
 - due to backtracking schemes, we need a bunch of combintors
 -
 - how to deal with sup-optimal backtracking, without having to use (*||) ?

(<||)   :: Single a -> List b   -> List b         -- co-optimal backtracking
(*||)   :: Vector a -> List b   -> List (a,b)     -- classified co-optimal backtracking
(***)   :: Single a -> Single b -> Vector (a,b)   -- classified DP

-}

bpmax :: Monad m => Nussinov m Char Int Int
bpmax = Nussinov
  { unp = \ x c     -> x
  , jux = \ x c y d -> if c `pairs` d then x + y + 1 else -999999
  , nil = \ ()      -> 0
  , h   = SM.foldl' max (-999999)
  }
{-# INLINE bpmax #-}

prob :: Monad m => Nussinov m Char Double Double
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

pretty :: Monad m => Nussinov m Char String [String] -- (SM.Stream m String)
pretty = Nussinov
  { unp = \ x c     -> x ++ "."
  , jux = \ x c y d -> x ++ "(" ++ y ++ ")"
  , nil = \ ()      -> ""
  , h   = SM.toList -- return . id
  }
{-# INLINE pretty #-}

prettyL :: Monad m => Nussinov m Char String String
prettyL = Nussinov
  { unp = \ x c     -> x ++ "."
  , jux = \ x c y d -> x ++ "(" ++ y ++ ")"
  , nil = \ ()      -> ""
  , h   = SM.head -- return . id
  }
{-# INLINE prettyL #-}

-- grammar :: Nussinov m Char () x r -> c' -> t' -> (t', Subword -> m r)
grammar Nussinov{..} c t' =
  let t = t'  ( unp <<< t % c           |||
                jux <<< t % c % t % c   |||
                nil <<< Epsilon         ... h
              )
  in Z:.t
{-# INLINE grammar #-}

{-
outsideGrammar Nussinov{..} c s t' =
  let t = t'  ( unp <<< t % c         |||
                -- jux <<< t % c % s % c |||
                -- jux <<< s % c % t % c |||
                nil <<< Epsilon         ... h
              )
  in Z:.t
{-# INLINE outsideGrammar #-}
-}

runNussinov :: Int -> String -> (Int,[String])
runNussinov k inp = (d, take k bs) where -- . {- . S.toList . -} unId $ axiom b) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.t) = runInsideForward i
  -- d = let (ITbl _ _ arr _) = t in arr PA.! subword 0 n
  d = iTblArray t PA.! subword 0 n
  bs = runInsideBacktrack i t
--  !(Z:.b) = grammar (bpmax <|| pretty) (chr i) (toBacktrack t (undefined :: Id a -> Id a))
{-# NOINLINE runNussinov #-}

runInsideForward :: VU.Vector Char -> Z:.ITbl Id Unboxed Subword Int
runInsideForward i = mutateTablesDefault
                   $ grammar bpmax
                       (chr i)
                       (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
  where n = VU.length i
{-# NoInline runInsideForward #-}

runInsideBacktrack :: VU.Vector Char -> ITbl Id Unboxed Subword Int -> [String]
runInsideBacktrack i t = unId $ axiom b
  where !(Z:.b) = grammar (bpmax <|| pretty) (chr i) (toBacktrack t (undefined :: Id a -> Id a))
{-# NoInline runInsideBacktrack #-}

--runInsideBacktrackL :: VU.Vector Char -> Z:.ITbl Id Unboxed Subword Int -> [String]
--runInsideBacktrackL i t = axiom b
--  where
--  !(Z:.b) = grammar (bpmax <|| prettyL) (chr i) (toBacktrack t (undefined :: Id a -> Id a))

{-
runPartitionNussinov :: String -> [(Subword,Double,Double,Double)]
runPartitionNussinov inp
  = Data.List.map (\(sh,a) -> let b = iTblArray t PA.! (O sh)
                              in (sh, a, b, a*b/d)
                  ) (PA.assocs $ iTblArray s)
  where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  s :: ITbl Id Unboxed Subword Double
  !(Z:.s) = mutateTablesDefault
          $ grammar prob
              (chr i)
              (ITbl EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) 0 []))
              
  d = iTblArray s PA.! subword 0 n
  t :: ITbl Id Unboxed (Outside Subword) Double
  !(Z:.t) = mutateTablesDefault
          $ outsideGrammar prob
              (chr i)
              --(undefined :: ITbl Id Unboxed (Outside Subword) Double)
              s
              (ITbl EmptyOk (PA.fromAssocs (O $ subword 0 0) (O $ subword 0 n) (-1) []))
{-# NOINLINE runPartitionNussinov #-}
-}

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runNussinov k l
    mapM_ (\x -> printf "%s %5d\n" x s) xs

