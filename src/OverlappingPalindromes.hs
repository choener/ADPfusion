
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
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Printf

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion



data Signature m x r c = Signature
  { ovrlap :: () -> () -> x -> x -> () -> x -- TODO !!!
  , brckts :: (Z:.c:.()) -> x -> (Z:.():.c) -> x
  , braces :: (Z:.c:.()) -> x -> (Z:.():.c) -> x
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

grammar Signature{..} x' a' b' i =
  let x = TW x' ( ovrlap <<< (split (Proxy :: Proxy "a") (Proxy :: Proxy Fragment) a)
                          %  (split (Proxy :: Proxy "b") (Proxy :: Proxy Fragment) b)
                          %  (split (Proxy :: Proxy "a") (Proxy :: Proxy Final   ) a)
                          %  (split (Proxy :: Proxy "b") (Proxy :: Proxy Final   ) b)
                          %  (split (Proxy :: Proxy "c") (Proxy :: Proxy Fragment) b) ... h
              )
      a = TW a' ( nilnil <<< (M:|Epsilon:|Epsilon)                           |||
                  brckts <<< (M:|chr i:|Deletion) % a % (M:|Deletion:|chr i) ... h
                )
      b = TW b' ( nilnil <<< (M:|Epsilon:|Epsilon)                           |||
                  braces <<< (M:|chr i:|Deletion) % b % (M:|Deletion:|chr i) ... h
                )
  in Z:.x:.a:.b
{-# Inline grammar #-}



score :: Monad m => Signature m Int Int Char
score = Signature
  { ovrlap = \ a' b' a b _ -> {- if a>0 || b>0 then traceShow ("oo",a',b',a,b) $ a + b else -} a+b -- TODO !!!
  , brckts = \ (Z:.l:.()) a (Z:.():.r) -> {- traceShow ("[]",l,a,r) $ -} if l=='[' && r==']' then a+1 else -999999
  , braces = \ (Z:.l:.()) b (Z:.():.r) -> {- traceShow ("()",l,b,r) $ -} if l=='(' && r==')' then b+1 else -999999
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
  { ovrlap = \ () () [a,a'] [b,b'] () -> [a ++ b ++ a' ++ b'] -- TODO !!!
  , brckts = \ (Z:.l:.()) [a,a'] (Z:.():.r) -> ["a"++a , a'++"A"]
  , braces = \ (Z:.l:.()) [b,b'] (Z:.():.r) -> ["b"++b , b'++"B"]
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
  b :: T
  (Z:.x:.a:.b) = opForward i
  (Z:.x':.a':.b') = grammar (score <|| pretty)
                      (toBacktrack x (undefined :: Id a -> Id a))
                      (toBacktrack a (undefined :: Id a -> Id a))
                      (toBacktrack b (undefined :: Id a -> Id a))
                      i
                      :: Z:.XB:.TB:.TB
{-# NoInline overlappingPalindromes #-}

opForward :: VU.Vector Char -> Z:.X:.T:.T
opForward i =
  let n = VU.length i
  in  mutateTablesDefault $
        grammar score
        (ITbl 1 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
        i
{-# NoInline opForward #-}

type X = TwITbl Id Unboxed EmptyOk (Subword I) Int
type T = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int

type XB = TwITblBt Unboxed EmptyOk (Subword I) Int Id Id [String]
type TB = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int Id Id [String]

main :: IO ()
main = do
  xs <- fmap lines $ getContents
  forM_ xs $ \x -> do
    let (d,bs) = overlappingPalindromes x
    putStrLn x
    print d
--    putStrLn $ head $ head bs

