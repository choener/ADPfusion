
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



data Nussinov m x r c = Nussinov
  { unp :: x -> c -> x
  , jux :: x -> c -> x -> c -> x
  , pse :: () -> () -> x -> x -> x
  , nil :: () -> x
  , pkn :: (Z:.x:.()) -> (Z:.c:.()) -> x -> (Z:.():.x) -> (Z:.():.c) -> x
  , h   :: SM.Stream m x -> m r
  }

--makeAlgebraProduct ''Nussinov


bpmax :: Monad m => Nussinov m Int Int Char
bpmax = Nussinov
  { unp = \ x c     -> x
  , jux = \ x c y d -> if c `pairs` d then x + y + 1 else -999999
  , pse = \ () () x y -> x + y
  , nil = \ ()      -> 0
  , pkn = \ (Z:.x:.()) (Z:.a:.()) y (Z:.():.z) (Z:.():.b) -> if a `pairs` b then x + y + z + 1 else -888888
  , h   = SM.foldl' max (-999999)
  }
{-# INLINE bpmax #-}

{-
prob :: Monad m => Nussinov m Double Double Char
prob = Nussinov
  { unp = \ x c     -> 0.3 * x
  , jux = \ x c y d -> 0.6 * if c `pairs` d then x * y else 0
  , nil = \ ()      -> 0.1
  , h   = SM.foldl' (+) 0
  }
-}

-- |

pairs !c !d
  =  c=='A' && d=='U'
  || c=='C' && d=='G'
  || c=='G' && d=='C'
  || c=='G' && d=='U'
  || c=='U' && d=='A'
  || c=='U' && d=='G'
{-# INLINE pairs #-}

{-
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
-}

grammar Nussinov{..} t' u' v' c =
  let t = t'  ( unp <<< t % c           |||
                jux <<< t % c % t % c   |||
                nil <<< Epsilon         |||
                pse <<< (split (Proxy :: Proxy "U") (Proxy :: Proxy Fragment) u)
                     %  (split (Proxy :: Proxy "V") (Proxy :: Proxy Fragment) v)
                     %  (split (Proxy :: Proxy "U") (Proxy :: Proxy Final)    u)
                     %  (split (Proxy :: Proxy "V") (Proxy :: Proxy Final)    v)  ... h
              )
      u = u'  ( pkn <<< (M:|t:|Deletion) % (M:|chr c:|Deletion) % u % (M:|Deletion:|t) % (M:|Deletion:|chr c) ... h
              )
      v = v'  ( pkn <<< (M:|t:|Deletion) % (M:|chr c:|Deletion) % u % (M:|Deletion:|t) % (M:|Deletion:|chr c) ... h
              )
  in Z:.t:.u:.v
{-# INLINE grammar #-}

{-
runNussinov :: Int -> String -> (Int,[String])
runNussinov k inp = (d, take k bs) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.t) = runInsideForward i
  d = unId $ axiom t
  bs = runInsideBacktrack i t
{-# NOINLINE runNussinov #-}
-}

type X = ITbl Id Unboxed Subword Int
type T = ITbl Id Unboxed (Z:.Subword:.Subword) Int

runInsideForward :: VU.Vector Char -> Z:.X:.T:.T
runInsideForward i = mutateTablesDefault
                   $ grammar bpmax
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
                        i
  where n = VU.length i
{-# NoInline runInsideForward #-}

{-
runInsideBacktrack :: VU.Vector Char -> ITbl Id Unboxed Subword Int -> [String]
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

-}


{-

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
  let x = x'  ( ovrlap <<< (split (Proxy :: Proxy "a") (Proxy :: Proxy Fragment) a)
                        %  (split (Proxy :: Proxy "b") (Proxy :: Proxy Fragment) b)
                        %  (split (Proxy :: Proxy "a") (Proxy :: Proxy Final   ) a)
                        %  (split (Proxy :: Proxy "b") (Proxy :: Proxy Final   ) b) -- ... h
                        %  (split (Proxy :: Proxy "c") (Proxy :: Proxy Fragment) b) ... h
              )
      a = a'  ( nilnil <<< (M:|Epsilon:|Epsilon)                           |||
                brckts <<< (M:|chr i:|Deletion) % a % (M:|Deletion:|chr i) ... h
              )
      b = b'  ( nilnil <<< (M:|Epsilon:|Epsilon)                           |||
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
  {-
  (Z:.x:.a:.b) = mutateTablesDefault $
                   grammar score
                   (ITbl 1 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-999999) []))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-999999) []))
                   i
                   -}
  (Z:.x':.a':.b') = grammar (score <|| pretty)
                      (toBacktrack x (undefined :: Id a -> Id a))
                      (toBacktrack a (undefined :: Id a -> Id a))
                      (toBacktrack b (undefined :: Id a -> Id a))
                      i
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

-}

