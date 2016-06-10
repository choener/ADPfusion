
module ADP.Fusion.Term.Strng.Subword where

import           Data.Proxy
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import           Prelude hiding (map)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Strng.Type



instance
  ( TmkCtx1 m ls (Strng v x) (Subword i)
  ) => MkStream m (ls :!: Strng v x) (Subword i) where
  mkStream (ls :!: strng) sv us is
    = S.map (\(ss,ee,ii) -> ElmStrng ee ii ss)
    . addTermStream1 strng sv us is
    $ mkStream ls (termStaticVar strng sv is) us (termStreamIndex strng sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (Subword I)
  ) => TermStream m (TermSymbol ts (Strng v x)) s (is:.Subword I) where
  --
  termStream (ts:|Strng f minL maxL v) (cs:.IStatic d) (us:.Subword (ui:.uj)) (is:.Subword (i:.j))
    = S.filter (\(TState s _ _) ->
                    -- let Subword (k:.l) = getIndex a (Proxy :: Proxy (is:.Subword I))
                    let RiSwI l = getIndex (getIdx s) (Proxy :: PRI is (Subword I))
                    in j-l <= maxL)
    . S.map (\(TState s ii ee) ->
                --let Subword (_:.l) = getIndex a (Proxy :: Proxy (is:.Subword I))
                --    o              = getIndex b (Proxy :: Proxy (is:.Subword I))
                let RiSwI l = getIndex (getIdx s) (Proxy :: PRI is (Subword I))
                in  TState s (ii:.:RiSwI j) (ee:.f l (j-l) v) )
    . termStream ts cs us is
  --
  termStream (ts:|Strng f minL maxL v) (cs:.IVariable d) (us:._) (is:.Subword (i:.j))
    = S.flatten mk step . termStream ts cs us is
    where mk (tstate@(TState s ii ee)) =
            let RiSwI k = getIndex (getIdx s) (Proxy :: PRI is (Subword I))
            in  return (tstate, k+minL, min j (k+maxL), k+minL)
          step ( TState s ii ee, minK, maxK, curK )
            | curK > maxK = return $ S.Done
            | otherwise   = let RiSwI k = getIndex (getIdx s) (Proxy :: PRI is (Subword I))
                            in  do return $ S.Yield (TState s (ii:.:RiSwI curK) (ee:.f k (curK-k) v)) (TState s ii ee, minK, maxK, curK +1)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

-- | TODO this is almost certainlywrong

instance TermStaticVar (Strng v x) (Subword I) where
  termStaticVar _ (IStatic d) _ = IVariable d
  termStaticVar _ (IVariable d) _ = IVariable d
  termStreamIndex _ _ (Subword (i:.j)) = subword i (j-1)
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

{-

-- | TODO If we use (IVariable mx) we might be able to request @exactly@
-- the range we need!

instance
  ( Monad m
  , Element ls (Subword I)
  , MkStream m ls (Subword I)
  ) => MkStream m (ls :!: Strng v x) (Subword I) where
  mkStream (ls :!: Strng slice mn mx v) (IStatic ()) hh (Subword (i:.j))
    = S.filter (\s -> let Subword (k:.l) = getIdx s in l-k <= mx)
    . S.map (\s -> let (Subword (_:.l)) = getIdx s
                   in  ElmStrng (slice l (j-l) v) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - mn))
  mkStream (ls :!: Strng slice mn mx v) (IVariable ()) hh (Subword (i:.j))
    = S.flatten mk step $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - mn))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - mn)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ S.Yield (ElmStrng (slice k (l-k) v) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ S.Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

-}

