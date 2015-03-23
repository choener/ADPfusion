
module ADP.Fusion.SynVar.Recursive
  ( module ADP.Fusion.SynVar.Recursive.Type
  , module ADP.Fusion.SynVar.Recursive.Point
  , module ADP.Fusion.SynVar.Recursive.Subword
  ) where

import ADP.Fusion.SynVar.Recursive.Point
import ADP.Fusion.SynVar.Recursive.Subword
import ADP.Fusion.SynVar.Recursive.Type


{-


-- * Instances

{-
instance ModifyConstraint (IRec m Subword x) where
  toNonEmpty (IRec _ iF iT f) = IRec NonEmpty iF iT f
  toEmpty    (IRec _ iF iT f) = IRec EmptyOk  iF iT f
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty    #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: IRec m Subword x) Subword where
  mkStream (ls :!: IRec c _ _ f) Static lu (Subword (i:.j))
    = let ms = minSize c in ms `seq`
    S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  f lu (subword l j) >>= \z -> return $ ElmIRec z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) lu (subword i $ j - ms)
  mkStream (ls :!: IRec c _ _ f) (Variable _ Nothing) lu (Subword (i:.j))
    = let ms = minSize c
          mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- f lu (subword k (j-z))
                             return $ S.Yield (ElmIRec y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) lu (subword i j)
  {-# INLINE mkStream #-}

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  ) => MkStream mB (ls :!: BT (IRec mF Subword x) mF mB r) Subword where
  mkStream (ls :!: BtIRec c _ _ f bt) Static lu (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      S.mapM (\s -> let (Subword (_:.l)) = getIdx s
                        ix               = subword l j
                    in  f lu ix >>= \fx -> return $ ElmBtIRec fx (bt lu ix) ix s)
      $ mkStream ls (Variable Check Nothing) lu (subword i $ j-ms)
  mkStream (ls :!: BtIRec c _ _ f bt) (Variable _ Nothing) lu (Subword (i:.j))
    = let ms = minSize c
          mk s = let Subword (_:.l) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let Subword (_:.k) = getIdx s
                                 ix             = subword k (j-z)
                             f lu ix >>= \fx -> return $ S.Yield (ElmBtIRec fx (bt lu ix) ix s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) lu (subword i j)
  {-# INLINE mkStream #-}
-}

-}

