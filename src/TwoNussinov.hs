
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | Nussinovs RNA secondary structure prediction algorithm via basepair
-- maximization.
--
-- The two-synvar version of Nussinov is used to determine if fusion
-- persists over multiple syntactic variables.

module Main where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           Text.Printf

import           Data.Array.Repa.Index.Subword
import           Data.PrimitiveArray as PA
import           Data.PrimitiveArray.Zero as PA

import           ADP.Fusion



data Nussinov m c e x r = Nussinov
  { unp :: x -> c -> x
  , jux :: x -> c -> x -> c -> x
  , nil :: e -> x
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

bpmax :: Monad m => Nussinov m Char () Int Int
bpmax = Nussinov
  { unp = \ x c     -> x
  , jux = \ x c y d -> if c `pairs` d then x + y + 1 else -999999
  , nil = \ ()      -> 0
  , h   = SM.foldl' max (-999999)
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

pretty :: Monad m => Nussinov m Char () String (SM.Stream m String)
pretty = Nussinov
  { unp = \ x c     -> x ++ "."
  , jux = \ x c y d -> x ++ "(" ++ y ++ ")"
  , nil = \ ()      -> ""
  , h   = return . id
  }
{-# INLINE pretty #-}

-- grammar :: Nussinov m Char () x r -> c' -> t' -> (t', Subword -> m r)
grammar Nussinov{..} (!c) s' t' =
  let s = s'  ( unp <<< t % c           |||
                jux <<< t % c % t % c   |||
                nil <<< Empty           ... h
              )
      t = t'  ( unp <<< s % c           |||
                jux <<< s % c % s % c   |||
                nil <<< Empty           ... h
              )
  in Z:.s:.t
{-# INLINE grammar #-}

runNussinov' :: Int -> String -> (Int,[String])
runNussinov' k inp = (d, take k . S.toList . unId $ axiom b) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  -- NOTE we need to fix the types at least once (@Subword@ and others),
  -- this we do here
  !(Z:.s:.t) = mutateTablesDefault
             $ grammar bpmax
                 (chr i)
                 (ITbl EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
                 (ITbl EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) [])) :: Z :. ITbl Id Unboxed Subword Int :. ITbl Id Unboxed Subword Int
  d = let (ITbl _ arr _) = t in arr PA.! subword 0 n
  !(Z:.b:.c) = grammar (bpmax <** pretty) (chr i) (toBT s (undefined :: Id a -> Id a)) (toBT t (undefined :: Id a -> Id a))
{-# NOINLINE runNussinov' #-}

{-
forward :: VU.Vector Char -> ST s (Z:.Unboxed Subword Int)
forward inp = do
  let n  = VU.length inp
  let c  = chr inp
  !t' <- PA.newWithM (subword 0 0) (subword 0 n) (-999999)
  let t  = MTbl EmptyOk t'
  runFreezeMTbls $ grammar bpmax c t
{-# NOINLINE forward #-}

backtrack :: VU.Vector Char -> PA.Unboxed Subword Int -> [String]
backtrack i t' = unId . SM.toList . unId $ axiom g where
  c = chr i
  (Z:.g) = grammar (bpmax <** pretty) c (BtTbl EmptyOk t')
{-# NOINLINE backtrack #-}

runNussinov :: Int -> String -> (Int,[String])
runNussinov k inp = (t PA.! (subword 0 n), take k b) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  (Z:.t) = runST $ forward i
  b = backtrack i t
{-# NOINLINE runNussinov #-}
-}

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runNussinov' k l
    mapM_ (\x -> printf "%s %5d\n" x s) xs

