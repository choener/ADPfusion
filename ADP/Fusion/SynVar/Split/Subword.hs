
-- |
--
-- TODO Rewrite to use the new index-generating system.
--
-- TODO Take care of minsize constraints! These are somewhat tricky. We
-- have one constraint for dimension in the table.

module ADP.Fusion.SynVar.Split.Subword where

import Data.Strict.Tuple
import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
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
import ADP.Fusion.SynVar.TableWrap



-- * 'Fragment' and 'Final' instances for 'Split' / 'ITbl'.

instance
  ( Monad m
  , Element ls (Subword I)
  , MkStream m ls (Subword I)
  ) => MkStream m (ls :!: Split uId Fragment (TwITbl m arr c j x)) (Subword I) where
  mkStream (ls :!: Split _) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let RiSwI l = getIdx s
                 in  ElmSplitITbl Proxy () (RiSwI j) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see above) - minSize c))
    where mk s = let RiSwI l = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let RiSwI k = getIdx s
                                        l       = j - z
                                        kl      = subword k l
                                    return $ Yield (ElmSplitITbl Proxy () (RiSwI l) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Subword I)
  , MkStream m ls (Subword I)
  , SplitIxCol uId (SameSid uId (Elm ls (Subword I))) (Elm ls (Subword I))
  , (SplitIxTy uId (SameSid uId (Elm ls (Subword I))) (Elm ls (Subword I)) :. Subword I) ~ mix
  , (PrimArrayOps arr (SplitIxTy uId (SameSid uId (Elm ls (Subword I))) (Elm ls (Subword I)) :. Subword I) x)
  , MinSize c
  ) => MkStream m (ls :!: Split uId Final (TwITbl m arr (cs:.c) mix x)) (Subword I) where
  mkStream (ls :!: Split (TW (ITbl _ _ (_:.c) t) _)) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let RiSwI l = getIdx s
                     fmbkm :: mix = collectIx (Proxy :: Proxy uId) s :. subword l j
                 in  ElmSplitITbl Proxy (t ! fmbkm) (RiSwI j) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: Split (TW (ITbl _ _ (_:.c) t) _)) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let RiSwI l = getIdx s in return (s :. (delay_inline id $ j - l - minSize c))
          step (s:.z) | z >= 0 = do let RiSwI k      = getIdx s
                                        l            = j - z
                                        kl           = subword k l
                                        fmbkm :: mix = collectIx (Proxy :: Proxy uId) s :. kl
                                    return $ Yield (ElmSplitITbl Proxy (t ! fmbkm) (RiSwI l) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}



-- * 'Fragment' and 'Final' instances for 'Split' / @Backtrack@ 'ITbl'.

instance
  ( Monad mB
  , Element ls (Subword I)
  , MkStream mB ls (Subword I)
  ) => MkStream mB (ls :!: Split uId Fragment (TwITblBt arr c j x mF mB r)) (Subword I) where
  mkStream (ls :!: Split (TW (BtITbl _ _) _)) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let RiSwI l = getIdx s
                 in  ElmSplitBtITbl Proxy () (RiSwI j) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see TODO in @Split@) - minSize c))
  mkStream (ls :!: Split _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j)) -- TODO (see above) - minSize c))
    where mk s = let RiSwI l = getIdx s in return (s :. j - l) -- TODO - minSize c)
          step (s:.z) | z >= 0 = do let RiSwI k = getIdx s
                                        l       = j - z
                                        kl      = subword k l
                                    return $ Yield (ElmSplitBtITbl Proxy () (RiSwI l) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (Subword I)
  , MkStream mB ls (Subword I)
  , SplitIxCol uId (SameSid uId (Elm ls (Subword I))) (Elm ls (Subword I))
  , (SplitIxTy uId (SameSid uId (Elm ls (Subword I))) (Elm ls (Subword I)) :. Subword I) ~ mix
  , (PrimArrayOps arr (SplitIxTy uId (SameSid uId (Elm ls (Subword I))) (Elm ls (Subword I)) :. Subword I) x)
  , MinSize c
  ) => MkStream mB (ls :!: Split uId Final (TwITblBt arr (cs:.c) mix x mF mB r)) (Subword I) where
  mkStream (ls :!: Split (TW (BtITbl (_:.c) t) bt)) (IStatic ()) hh (Subword (i:.j))
    = mapM (\s -> let RiSwI l      = getIdx s
                      lj           = subword l j
                      fmbkm :: mix = collectIx (Proxy :: Proxy uId) s :. lj
                      (_,hhhh)     = bounds t -- This is an ugly hack, but we need a notation of higher bound from somewhere
                  in  bt hhhh fmbkm >>= \ ~bb -> return $ ElmSplitBtITbl Proxy (t ! fmbkm,bb) (RiSwI j) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: Split (TW (BtITbl (_:.c) t) bt)) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j))
    where mk s = let RiSwI l = getIdx s in return (s :. (delay_inline id $ j - l - minSize c))
          step (s:.z) | z >= 0 = do let RiSwI k      = getIdx s
                                        l            = j - z
                                        kl           = subword k l
                                        fmbkm :: mix = collectIx (Proxy :: Proxy uId) s :. kl
                                        (_,hhhh)     = bounds t -- same ugly hack
                                    bt hhhh fmbkm >>= \ ~bb -> return $ Yield (ElmSplitBtITbl Proxy (t ! fmbkm,bb) (RiSwI l) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

