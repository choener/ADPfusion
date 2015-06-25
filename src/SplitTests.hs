
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds               #-}
{-# Language DefaultSignatures       #-}
{-# Language FlexibleContexts        #-}
{-# Language FlexibleInstances       #-}
{-# Language GADTs                   #-}
{-# Language KindSignatures          #-}
{-# Language MultiParamTypeClasses   #-}
{-# Language RankNTypes              #-}
{-# Language StandaloneDeriving      #-}
{-# Language TemplateHaskell         #-}
{-# Language TypeFamilies            #-}
{-# Language TypeOperators           #-}
{-# Language TypeSynonymInstances    #-}
{-# Language UndecidableInstances    #-}

module Main where

import           Control.Applicative
import           Control.Monad
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Control.Arrow as A
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Printf

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion



data Signature m x r c = Signature
  { ovrlap :: () -> x -> x
  , brckts :: (Z:.c:.()) -> x -> (Z:.():.c) -> x
  , nilnil :: (Z:.():.()) -> x
  , h :: Stream m x -> m r
  }

makeAlgebraProduct ''Signature



-- |
--
-- @
-- 012345678
-- [[((]]))
-- @

grammar Signature{..} x' a' i =
  let x = x'  ( ovrlap <<< (split (Proxy :: Proxy "a") (Proxy :: Proxy Fragment) a)
                        %  (split (Proxy :: Proxy "a") (Proxy :: Proxy Final   ) a) ... h
              )
      a = a'  ( nilnil <<< (M:|Epsilon:|Epsilon)                           |||
                brckts <<< (M:|chr i:|Deletion) % a % (M:|Deletion:|chr i) ... h
              )
  in Z:.x:.a
{-# Inline grammar #-}



score :: Monad m => Signature m Int Int Char
score = Signature
  { ovrlap = \ a' a -> a + 4711
  , brckts = \ (Z:.l:.()) a (Z:.():.r) -> {- traceShow ("[]",l,a,r) $ -} if l=='[' && r==']' then a+1 else -999999
  , nilnil = \ _ -> 0
  , h = SM.foldl' max (-999999)
  }
{-# Inline score #-}



-- |
--
-- TODO pretty shows in @ovrlap@ that we might want to introduce a second
-- @h@ together with @Stream m y -> m s@?

pretty :: Monad m => Signature m [String] [[String]] Char
pretty = Signature
  { ovrlap = \ () [a,a'] -> [a ++ a']
  , brckts = \ (Z:.l:.()) [a,a'] (Z:.():.r) -> ["a"++a , a'++"A"]
  , nilnil = \ _ -> ["",""]
  , h = SM.toList
  }
{-# Inline pretty #-}



overlappingPalindromes :: String -> (Int,[[String]])
overlappingPalindromes inp = (d,bs) where
  i  = VU.fromList inp
  n  = VU.length i
  d  = unId $ axiom x
  bs = unId $ axiom x'
  x :: X
  a :: T
  (Z:.x:.a) = opForward i
  (Z:.x':.a') = grammar (score <|| pretty)
                  (toBacktrack x (undefined :: Id a -> Id a))
                  (toBacktrack a (undefined :: Id a -> Id a))
                  i
{-# NoInline overlappingPalindromes #-}

opForward :: VU.Vector Char -> Z:.X:.T
opForward i =
  let n = VU.length i
  in  mutateTablesDefault $
        grammar score
        (ITbl 1 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
        i
{-# NoInline opForward #-}

type X = ITbl Id Unboxed Subword Int
type T = ITbl Id Unboxed (Z:.Subword:.Subword) Int


main :: IO ()
main = do
  xs <- fmap lines $ getContents
  forM_ xs $ \x -> do
    let (d,bs) = overlappingPalindromes x
    putStrLn x
    print d
--    putStrLn $ head $ head bs

