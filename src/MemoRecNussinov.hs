
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

import           ADP.Fusion.Point



data Nussinov m c e x r = Nussinov
  { unp :: x -> c -> x
  , jux :: x -> c -> x -> c -> x
  , nil :: e -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Nussinov

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

runNussinov :: Int -> String -> (Int,[String])
runNussinov k inp = (d, take k . S.toList . unId $ axiom b) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  -- NOTE we need to fix the types at least once (@Subword@ and others),
  -- this we do here
  !(Z:.s:.t) = mutateTablesDefault
             $ grammar bpmax
                 (chr i)
                 (ITbl EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
                 (IRec EmptyOk (subword 0 0) (subword 0 n)                              ) :: Z :. ITbl Id Unboxed Subword Int :. IRec Id Subword Int
  d = let (ITbl _ arr _) = s in arr PA.! subword 0 n
  !(Z:.b:.c) = grammar (bpmax <** pretty) (chr i) (toBT s (undefined :: Id a -> Id a)) (toBT t (id :: Id a -> Id a))
{-# NOINLINE runNussinov #-}

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runNussinov k l
    mapM_ (\x -> printf "%s %5d\n" x s) xs

