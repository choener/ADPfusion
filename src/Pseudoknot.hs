
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
  , nll :: (Z:.():.()) -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProduct ''Nussinov


bpmax :: Monad m => Nussinov m Int Int Char
bpmax = Nussinov
  { unp = \ x c     -> x
  , jux = \ x c y d -> if c `pairs` d then x + y + 1 else -999999
  , pse = \ () () x y -> x + y
  , nil = \ ()      -> 0
  , pkn = \ (Z:.x:.()) (Z:.a:.()) y (Z:.():.z) (Z:.():.b) -> if (a `pairs` b || a == 'N' && b == 'M') then x + y + z + 1 else -888888
  , nll = \ (Z:.():.()) -> 0
  , h   = SM.foldl' max (-999999)
  }
{-# INLINE bpmax #-}

-- |

pairs !c !d
  =  c=='A' && d=='U'
  || c=='C' && d=='G'
  || c=='G' && d=='C'
  || c=='G' && d=='U'
  || c=='U' && d=='A'
  || c=='U' && d=='G'
{-# INLINE pairs #-}

-- |
--
-- TODO It could be beneficial to introduce
-- @type Splitted = Either String (String,String)@
-- or something isomorphic. While [String] works, it allows for too many
-- possibilities here! ([] ist lightweight, on the other hand ...)

pretty :: Monad m => Nussinov m [String] [[String]] Char
pretty = Nussinov
  { unp = \ [x] c     -> [x ++ "."]
  , jux = \ [x] c [y] d -> [x ++ "(" ++ y ++ ")"]
  , pse = \ () () [x1,x2] [y1,y2] -> [x1 ++ y1 ++ x2 ++ y2]
  , nil = \ ()      -> [""]
  , pkn = \ (Z:.[x]:.()) (Z:.a:.()) [y1,y2] (Z:.():.[z]) (Z:.():.b) -> [x ++ "[" ++ y1 , y2 ++ z ++ "]"]
  , nll = \ (Z:.():.()) -> ["",""]
  , h   = SM.toList
  }
{-# INLINE pretty #-}

grammar Nussinov{..} t' u' v' c =
  let t = t'  ( unp <<< t % chr c               |||
                jux <<< t % chr c % t % chr c   |||
                nil <<< Epsilon                 |||
                pse <<< (split (Proxy :: Proxy "U") (Proxy :: Proxy Fragment) u)
                     %  (split (Proxy :: Proxy "V") (Proxy :: Proxy Fragment) v)
                     %  (split (Proxy :: Proxy "U") (Proxy :: Proxy Final)    u)
                     %  (split (Proxy :: Proxy "V") (Proxy :: Proxy Final)    v)  ... h
              )
      u = u'  ( pkn <<< (M:|t:|Deletion) % (M:|chr c:|Deletion) % u % (M:|Deletion:|t) % (M:|Deletion:|chr c) |||
                nll <<< (M:|Epsilon:|Epsilon)                                                                 ... h
              )
      v = v'  ( pkn <<< (M:|t:|Deletion) % (M:|chr c:|Deletion) % v % (M:|Deletion:|t) % (M:|Deletion:|chr c) |||
                nll <<< (M:|Epsilon:|Epsilon)                                                                 ... h
              )
  in Z:.t:.u:.v
{-# INLINE grammar #-}

runPseudoknot :: Int -> String -> (Int,[String])
runPseudoknot k inp = (d, take k bs) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.t:.u:.v) = runInsideForward i
  d = unId $ axiom t
  bs = [] -- runInsideBacktrack i t
{-# NOINLINE runPseudoknot #-}

type X = ITbl Id Unboxed Subword Int
type T = ITbl Id Unboxed (Z:.Subword:.Subword) Int

runInsideForward :: VU.Vector Char -> Z:.X:.T:.T
runInsideForward i = mutateTablesDefault
                   $ grammar bpmax
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        i
  where n = VU.length i
{-# NoInline runInsideForward #-}

{-
runInsideBacktrack :: VU.Vector Char -> ITbl Id Unboxed Subword Int -> [String]
runInsideBacktrack i t = unId $ axiom b
  where !(Z:.b) = grammar (bpmax <|| pretty) (chr i) (toBacktrack t (undefined :: Id a -> Id a))
{-# NoInline runInsideBacktrack #-}
-}

main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    putStrLn l
    let (s,xs) = runPseudoknot k l
    print s
    mapM_ (\x -> printf "%s %5d\n" x s) xs

