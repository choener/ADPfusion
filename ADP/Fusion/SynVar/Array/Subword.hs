
{-# Language MagicHash #-}

module ADP.Fusion.SynVar.Array.Subword where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Data.Vector.Fusion.Stream.Monadic
import Debug.Trace
import Prelude hiding (map,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack

-- TODO think about what we are about to do
import GHC.Prim (reallyUnsafePtrEquality#)




-- TODO delay inline @(subword i $ j - minSize c)@ or face fusion-breakage.
-- Can we just have @Inline [0] subword@ to fix this?

instance
  ( Monad m
  , Element ls Subword
  , PrimArrayOps arr Subword x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: ITbl m arr Subword x) Subword where
  mkStream (ls :!: ITbl _ _ c t _) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                 in  ElmITbl (t ! subword l j) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: ITbl _ _ c t _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmITbl (t ! kl) kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  , PrimArrayOps arr Subword x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr Subword x) mF mB r) Subword where
  mkStream (ls :!: BtITbl c t bt) (IStatic ()) hh ij@(Subword (i:.j))
    = mapM (\s -> let Subword (_:.l) = getIdx s
                      lj             = subword l j
                  in  bt hh lj >>= \ ~bb -> return $ ElmBtITbl (t ! lj) (bb {-bt hh lj-}) lj (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: BtITbl c t bt) (IVariable ()) hh ij@(Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    bt hh kl >>= \ ~bb -> return $ Yield (ElmBtITbl (t ! kl) (bb {-bt hh kl-}) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}


instance
  ( Monad m
  , Element ls (Outside Subword)
  , PrimArrayOps arr (Outside Subword) x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr (Outside Subword) x) (Outside Subword) where
  -- TODO what about @c / minSize@
  mkStream (ls :!: ITbl _ _ c t _) (OStatic (di:.dj)) u ij@(O (Subword (i:.j)))
    = map (\s -> let O (Subword (k:._)) = getOmx s
                     kj = O $ Subword (k:.j+dj)
                 in  ElmITbl (t ! kj) (O $ Subword (i:.j+dj)) kj s) -- @ij@ or s.th. else shouldn't matter?
    $ mkStream ls (OFirstLeft (di:.dj)) u ij
  mkStream (ls :!: ITbl _ _ c t _) (ORightOf (di:.dj)) u@(O (Subword (_:.h))) ij@(O (Subword (i:.j)))
    = flatten mk step Unknown $ mkStream ls (OFirstLeft (di:.dj)) u ij
      where mk s = return (s:.j+dj)
            step (s:.l) | l <= h = do let (O (Subword (k:._))) = getIdx s
                                          kl = O $ Subword (k:.l)
                                      return $ Yield (ElmITbl (t ! kl) (O (Subword (j+dj:.j+dj))) kl s) (s:.l+1)
                        | otherwise = return $ Done
            {-# Inline [0] mk   #-}
            {-# Inline [0] step #-}
  mkStream (ls :!: ITbl _ _ c t _) (OFirstLeft d) u ij = error "Array/Outside Subword : OFirstLeft : should never be reached!"
  mkStream (ls :!: ITbl _ _ c t _) (OLeftOf d) u ij = error "Array/Outside Subword : OLeftOf : should never be reached!"
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls (Outside Subword)
  , PrimArrayOps arr Subword x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr Subword x) (Outside Subword) where
  -- TODO what about @c / minSize@
  mkStream (ls :!: ITbl _ _ c t _) (OStatic (di:.dj)) u ij@(O (Subword (i:.j)))
    = map (\s -> let O (Subword (_:.k))     = getIdx s
                     o@(O (Subword (_:.l))) = getOmx s
                     kl = Subword (k-dj:.l-dj)
                 in ElmITbl (t ! kl) (O (Subword (k:.l))) o s)
    $ mkStream ls (ORightOf (di:.dj)) u ij
  mkStream (ls :!: ITbl _ _ c t _) (ORightOf d) u@(O (Subword (_:.h))) ij@(O (Subword (i:.j)))
    = flatten mk step Unknown $ mkStream ls (ORightOf d) u ij
    where mk s = let O (Subword (_:.l)) = getIdx s
                 in  return (s :.l:.l + minSize c)
          step (s:.k:.l)
            | let O (Subword (_:.o)) = getOmx s
            , l <= o = do let kl = Subword (k:.l)
                          return $ Yield (ElmITbl (t ! kl) (O kl) (getOmx s) s) (s:.k:.l+1)
            | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  mkStream (ls :!: ITbl _ _ c t _) (OFirstLeft (di:.dj)) u ij@(O (Subword (i:.j)))
    = map (\s -> let O (Subword (l:._)) = getOmx s
                     O (Subword (_:.k)) = getIdx s
                     kl = Subword (k:.i-di)
                 in  ElmITbl (t ! kl) (O kl) (getOmx s) s)
    $ mkStream ls (OLeftOf (di:.dj)) u ij
  mkStream (ls :!: ITbl _ _ c t _) (OLeftOf d) u ij@(O (Subword (i:.j)))
    = flatten mk step Unknown $ mkStream ls (OLeftOf d) u ij
    where mk s = let O (Subword (_:.l)) = getIdx s in return (s:.l)
          step (s:.l) | l <= i = do let O (Subword (_:.k)) = getIdx s
                                        kl = Subword (k:.l)
                                    return $ Yield (ElmITbl (t ! kl) (O kl) (getOmx s) s) (s:.l+1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Complement Subword)
  , PrimArrayOps arr Subword x
  , MkStream m ls (Complement Subword)
  ) => MkStream m (ls :!: ITbl m arr Subword x) (Complement Subword) where
  mkStream (ls :!: ITbl _ _ c t _) Complemented u ij
    = map (\s -> let (C ix) = getIdx s
                 in  ElmITbl (t ! ix) (C ix) (getOmx s) s)
    $ mkStream ls Complemented u ij
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Complement Subword)
  , PrimArrayOps arr (Outside Subword) x
  , MkStream m ls (Complement Subword)
  ) => MkStream m (ls :!: ITbl m arr (Outside Subword) x) (Complement Subword) where
  mkStream (ls :!: ITbl _ _ c t _) Complemented u ij
    = map (\s -> let (C ox) = getOmx s      -- TODO shouldn't this be @getIdx@ as well? on the count of everything being terminals in Complement?
                 in  ElmITbl (t ! (O ox)) (getIdx s) (C ox) s)
    $ mkStream ls Complemented u ij
  {-# Inline mkStream #-}



instance ModifyConstraint (ITbl m arr Subword x) where
  toNonEmpty (ITbl b l _ arr f) = ITbl b l NonEmpty arr f
  toEmpty    (ITbl b l _ arr f) = ITbl b l EmptyOk  arr f
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}

instance ModifyConstraint (Backtrack (ITbl mF arr Subword x) mF mB r) where
  toNonEmpty (BtITbl _ arr bt) = BtITbl NonEmpty arr bt
  toEmpty    (BtITbl _ arr bt) = BtITbl EmptyOk  arr bt
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}



instance
  ( Monad m
  , Element ls Subword -- (Z:.Subword:.Subword)
  , FirstSecond ls (arr (Z:.Subword:.Subword) x)
  , PrimArrayOps arr (Z:.Subword:.Subword) x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: ITbl m arr (Z:.Subword:.Subword) x) Subword where
  mkStream (ls :!: ITbl _ _ c t elm) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                     ab               = if greenLight ls t
                                          then greenIdx ls t elm
                                          else subword 0 0
                 in  ElmITbl (t ! (Z:.ab:.subword l j)) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - 0))
  mkStream (ls :!: ITbl _ _ c t elm) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - 0))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - 0)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                        ab             = if greenLight ls t
                                                           then greenIdx ls t elm
                                                           else subword 0 0
                                    return $ Yield (ElmITbl (t ! (Z:.ab:.kl)) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

-- | Get the previous index; this should really be made generic!
--
-- TODO This is probably a REALLY STUPID IDEA ;-)

class FirstSecond x k where
  greenLight :: x -> k -> Bool

class FirstSecondIdx x k i where
  greenIdx :: x -> k -> RecElm x i -> Subword

instance FirstSecond S k where
  greenLight S _ = False

instance FirstSecondIdx x k i where
  greenIdx S _ _ = error "shouldn't arrive here!"

instance
  ( FirstSecond ls (arr (Z:.Subword:.Subword) x)
  ) => FirstSecond (ls :!: ITbl m arr (Z:.Subword:.Subword) x) (arr (Z:.Subword:.Subword) x) where
  greenLight (ls :!: ITbl _ _ _ t _) t' =
    case reallyUnsafePtrEquality# t t' of
      -- TODO speaking of stupid ideas!
      1# -> traceShow "True" True
      _  -> greenLight ls t'
  {-# Inline greenLight #-}

instance
  ( FirstSecondIdx ls (arr (Z:.Subword:.Subword) x) (Z:.Subword:.Subword)
  , Element ls Subword
  ) => FirstSecondIdx (ls :!: ITbl m arr (Z:.Subword:.Subword) x) (arr (Z:.Subword:.Subword) x) (Z:.Subword:.Subword) where
  greenIdx (ls :!: ITbl _ _ _ t elm) t' e =
    case reallyUnsafePtrEquality# t t' of
      1# -> getIdx e
      _  -> greenIdx ls t' (getElm elm)
  {-# Inline greenIdx   #-}

