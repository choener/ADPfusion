
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | Nussinovs RNA secondary structure prediction algorithm via basepair
-- maximization.

module Main where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List
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



data Nussinov m c e x r = Nussinov
  { unp :: x -> c -> x
  , jux :: x -> x -> x
  , pai :: c -> x -> c -> x
  , nil :: e -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Nussinov

bpmax :: Monad m => Nussinov m Char () Int Int
bpmax = Nussinov
  { unp = \ x c   -> x
  , jux = \ x y   -> x + y
  , pai = \ c x d -> if c `pairs` d then x+1 else (-999999)
  , nil = \ ()    -> 0
  , h   = SM.foldl' max (-999999)
  }
{-# INLINE bpmax #-}

prob :: Monad m => Nussinov m Char () Double Double
prob = Nussinov
  { unp = \ x c     -> 0.3 * x                                -- 'any'
  , jux = \ x y     -> 0.6 * x * y                            -- 'any'
  , pai = \ c x d   -> 1.0 * if c `pairs` d then x else 0     -- 'paired'
  , nil = \ ()      -> 0.1                                    -- 'any'
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

pretty :: Monad m => Nussinov m Char () String (SM.Stream m String)
pretty = Nussinov
  { unp = \ x c     -> x ++ "."
  , jux = \ x y     -> x ++ y
  , pai = \ c x d   -> "(" ++ x ++ ")"
  , nil = \ ()      -> ""
  , h   = return . id
  }
{-# INLINE pretty #-}

-- | The inside grammar is:
--
-- @
-- A -> A c
-- A -> A P
-- A -> empty
-- P -> c A c
-- @

-- insideGrammar :: Nussinov m Char () x r -> c' -> t' -> (t', Subword -> m r)
insideGrammar Nussinov{..} c a' p' =
  let a = a'  ( unp <<< a % c     |||
                jux <<< a % p     |||
                nil <<< Empty     ... h
              )
      p = p'  ( pai <<< c % a % c ... h
              )
  in Z:.a:.p
{-# INLINE insideGrammar #-}

-- | Given the inside grammar, the outside grammar is:
--
-- @
-- B -> B c
-- B -> B P
-- B -> empty
-- B -> c Q c
-- Q -> A B
-- @

outsideGrammar Nussinov{..} c a p b' q' =
  let b = b'  ( unp <<< b % c         |||
                jux <<< b % p         |||
                pai <<< c % q % c     |||
                nil <<< Empty         ... h
              )
      q = q'  ( jux <<< a % b         ... h
              )
  in Z:.b:.q
{-# INLINE outsideGrammar #-}

runNussinov :: String -> (Double,Double)
runNussinov inp = (d, e) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.a:.p) = runInsideForward i
  !(Z:.b:.q) = runOutsideForward i a p
  d = let (ITbl _ arr _) = a in arr PA.! subword 0 n
  e = let (ITbl _ arr _) = b in arr PA.! (O $ subword 0 n)  -- TODO this is wrong, because we need to sum up over all (i,i) pairs
--  !(Z:.b:.q) = insideGrammar (prob <** pretty) (chr i) (toBacktrack a (undefined :: Id a -> Id a)) (toBacktrack p (undefined :: Id a -> Id a))
{-# NOINLINE runNussinov #-}

type TblI = ITbl Id Unboxed          Subword  Double
type TblO = ITbl Id Unboxed (Outside Subword) Double

runInsideForward :: VU.Vector Char -> Z:.TblI:.TblI
runInsideForward i = mutateTablesDefault
                   $ insideGrammar prob
                       (chr i)
                       (ITbl EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) 0 []))
                       (ITbl EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) 0 []))
  where n = VU.length i
{-# NoInline runInsideForward #-}

runOutsideForward :: VU.Vector Char -> TblI -> TblI -> Z:.TblO:.TblO
runOutsideForward i a p = mutateTablesDefault
                        $ outsideGrammar prob
                            (chr i)
                            a p
                            (ITbl EmptyOk (PA.fromAssocs (O $ subword 0 0) (O $ subword 0 n) 0 []))
                            (ITbl EmptyOk (PA.fromAssocs (O $ subword 0 0) (O $ subword 0 n) 0 []))
  where n = VU.length i
{-# NoInline runOutsideForward #-}

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

main :: IO ()
main = do
  return ()
  {-
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runNussinov k l
    mapM_ (\x -> printf "%s %5d\n" x s) xs
  -}

