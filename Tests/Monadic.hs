
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Tests.Monadic where

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import           Data.Vector.Fusion.Util
import           Data.Vector.Fusion.Stream.Size
import           Control.Monad.Reader
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import           Control.Monad.Primitive (PrimState (..))
import           Control.Monad.ST
import qualified Data.Vector.Generic.New as New
import           Control.Monad
import           Control.Monad.Primitive.Class



type C m a = SM.Stream m a -> SM.Stream m a

optMax :: (Monad m, Ord a, Bounded a) => C m a
optMax = SM.replicateM 1 . SM.foldl' max minBound
{-# INLINE optMax #-}

optReaderMax :: forall m . (Monad m, MonadReader Int m) => C m Int
optReaderMax xs = SM.replicateM 1 $ do
  a <- ask
  ys <- unstreamUM xs
  return $ ys U.! a
{-# INLINE optReaderMax #-}

unstreamUM, booboo :: (Monad m, UM.Unbox a) => SM.Stream m a -> m (U.Vector a)
unstreamUM xs = do l <- SM.toList xs
                   return $ U.fromList l
{-# INLINE unstreamUM #-}

booboo xs = do
    let s = SM.size xs
    SM.foldl' U.snoc U.empty xs

test_001 :: Int -> Int
test_001 = unId . SM.head . optMax . flip SM.sized Unknown . SM.singleton
{-# NOINLINE test_001 #-}

test_002 :: Int -> Int
test_002 k = unId . SM.head . optMax . flip SM.sized Unknown $ SM.replicate k k
{-# NOINLINE test_002 #-}

test_003 :: Int -> Int
test_003 k = runReader (SM.head . optReaderMax $ SM.replicate k k) (k `div` 2)
{-# NOINLINE test_003 #-}

