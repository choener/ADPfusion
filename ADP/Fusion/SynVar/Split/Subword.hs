
module ADP.Fusion.SynVar.Split.Subword where

import Data.Strict.Tuple
import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import GHC.TypeLits
import Prelude hiding (map,mapM)
import Data.Type.Equality

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Split.Type



-- * 'Fragment' and 'Final' instances for 'Split' / 'ITbl'.

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Split uId Fragment (ITbl m arr j x)) Subword where
  mkStream (ls :!: Split _) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                 in  ElmSplitITbl Proxy () (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see above) - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmSplitITbl Proxy () kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  , SplitIxCol uId (SameSid uId (Elm ls Subword)) ls Subword
  , (SplitIxTy uId (SameSid uId (Elm ls Subword)) ls Subword :. Subword) ~ mix
  ,  (PrimArrayOps arr (SplitIxTy uId (SameSid uId (Elm ls Subword)) ls Subword :. Subword) x)
  ) => MkStream m (ls :!: Split uId Final (ITbl m arr mix x)) Subword where
  mkStream (ls :!: Split (ITbl _ _ c t elm)) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                     fmbkm :: mix = collectIx (Proxy :: Proxy uId) s :. subword l j
                 in  ElmSplitITbl Proxy (t ! fmbkm) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split (ITbl _ _ c t _)) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                        fmbkm :: mix   = collectIx (Proxy :: Proxy uId) s :. kl
                                    return $ Yield (ElmSplitITbl Proxy (t ! fmbkm) kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}



-- * 'Fragment' and 'Final' instances for 'Split' / @Backtrack@ 'ITbl'.

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  ) => MkStream mB (ls :!: Split uId Fragment (Backtrack (ITbl mF arr j x) mF mB r)) Subword where
  mkStream (ls :!: Split _) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                 in  ElmSplitBtITbl Proxy () (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see above) - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmSplitBtITbl Proxy () kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  , SplitIxCol uId (SameSid uId (Elm ls Subword)) ls Subword
  , (SplitIxTy uId (SameSid uId (Elm ls Subword)) ls Subword :. Subword) ~ mix
  , (PrimArrayOps arr (SplitIxTy uId (SameSid uId (Elm ls Subword)) ls Subword :. Subword) x)
  ) => MkStream mB (ls :!: Split uId Final (Backtrack (ITbl mF arr mix x) mF mB r)) Subword where
  mkStream (ls :!: Split (BtITbl c t bt)) (IStatic ()) hh (Subword (i:.j))
    = mapM (\s -> let (Subword (_:.l)) = getIdx s
                      lj               = subword l j
                      fmbkm :: mix     = collectIx (Proxy :: Proxy uId) s :. lj
                      (_,hhhh)         = bounds t -- This is an ugly hack, but we need a notation of higher bound from somewhere
                  in  bt hhhh fmbkm >>= \ ~bb -> return $ ElmSplitBtITbl Proxy (t ! fmbkm,bb) lj (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split (BtITbl c t bt)) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                        fmbkm :: mix   = collectIx (Proxy :: Proxy uId) s :. kl
                                        (_,hhhh)       = bounds t -- same ugly hack
                                    bt hhhh fmbkm >>= \ ~bb -> return $ Yield (ElmSplitBtITbl Proxy (t ! fmbkm,bb) kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

