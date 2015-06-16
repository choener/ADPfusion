
module ADP.Fusion.Term.Strng.Subword where


import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import           Prelude hiding (map)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Strng.Type



-- | TODO If we use (IVariable mx) we might be able to request @exactly@
-- the range we need!

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Strng v x) Subword where
  mkStream (ls :!: Strng slice mn mx v) (IStatic ()) hh (Subword (i:.j))
    = S.filter (\s -> let Subword (k:.l) = getIdx s in l-k <= mx)
    . S.map (\s -> let (Subword (_:.l)) = getIdx s
                   in  ElmStrng (slice l (j-l) v) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - mn))
  mkStream (ls :!: Strng slice mn mx v) (IVariable ()) hh (Subword (i:.j))
    = S.flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - mn))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - mn)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ S.Yield (ElmStrng (slice k (l-k) v) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ S.Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

