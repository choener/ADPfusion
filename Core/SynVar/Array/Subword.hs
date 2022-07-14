
module ADPfusion.SynVar.Array.Subword where

import Data.Proxy
import Data.Strict.Tuple hiding (snd)
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,mapM)

import Data.PrimitiveArray hiding (map)

import ADPfusion.Base
import ADPfusion.SynVar.Array.Type
import ADPfusion.SynVar.Backtrack
import ADPfusion.SynVar.Indices



instance
  ( Monad m
  , Element ls (i I)
  , PrimArrayOps arr u x
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.i I) (Z:.u) (Z:.i I)
  , TableStaticVar u (i I)
  , MkStream m ls (i I)
  ) => MkStream m (ls :!: ITbl m arr u x) (i I) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
  {-# Inline mkStream #-}

{-
instance
  ( Monad m
  , Element ls (Subword I)
  , PrimArrayOps arr u x
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.Subword I) (Z:.u) (Z:.Subword I)
  , MkStream m ls (Subword I)
  ) => MkStream m (ls :!: ITbl m arr u x) (Subword I) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
  {-# Inline mkStream #-}
-}

instance
  ( Monad mB
  , Element ls (i I)
  , MkStream mB ls (i I)
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.i I) (Z:.u) (Z:.i I)
  , TableStaticVar u (i I)
  , PrimArrayOps arr u x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr u x) mF mB r) (i I) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(s,ii,oo,ii',oo') -> bt us' ii >>= \ ~bb -> return $ ElmBtITbl (t!ii) bb ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
    where !us' = snd $ bounds t
  {-# Inline mkStream #-}

-- | An outside table in an outside index context.
--
-- TODO what about @c / minSize@

instance
  ( Monad m
  , Element ls (i O)
  , PrimArrayOps arr (u O) x
  , TblConstraint (u O) ~ TableConstraint
  , AddIndexDense (Z:.i O) (Z:.u O) (Z:.i O)
  , TableStaticVar (u O) (i O)
  , MkStream m ls (i O)
  ) => MkStream m (ls :!: ITbl m arr (u O) x) (i O) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!oo) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u O)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u O)) c vs is)
  {-# Inline mkStream #-}

-- | An inside table in an outside index context.

instance
  ( Monad m
  , Element ls (i O)
  , PrimArrayOps arr (u I) x
  , TblConstraint (u I) ~ TableConstraint
  , AddIndexDense (Z:.i O) (Z:.u I) (Z:.i O)
  , TableStaticVar (u I) (i O)
  , MkStream m ls (i O)
  ) => MkStream m (ls :!: ITbl m arr (u I) x) (i O) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u I)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u I)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (i C)
  , PrimArrayOps arr (u I) x
  , MkStream m ls (i C)
  , TblConstraint (u I) ~ TableConstraint
  , AddIndexDense (Z:.i C) (Z:.u I) (Z:.i C)
  , TableStaticVar (u I) (i C)
  ) => MkStream m (ls :!: ITbl m arr (u I) x) (i C) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u I)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u I)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (i C)
  , PrimArrayOps arr (u O) x
  , MkStream m ls (i C)
  , TblConstraint (u O) ~ TableConstraint
  , AddIndexDense (Z:.i C) (Z:.u O) (Z:.i C)
  , TableStaticVar (u O) (i C)
  ) => MkStream m (ls :!: ITbl m arr (u O) x) (i C) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!oo) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u O)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u O)) c vs is)
  {-# Inline mkStream #-}

{-
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
-}


instance ModifyConstraint (ITbl m arr (Subword t) x) where
  toNonEmpty (ITbl b l _ arr f) = ITbl b l NonEmpty arr f
  toEmpty    (ITbl b l _ arr f) = ITbl b l EmptyOk  arr f
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}

instance ModifyConstraint (Backtrack (ITbl mF arr (Subword t) x) mF mB r) where
  toNonEmpty (BtITbl _ arr bt) = BtITbl NonEmpty arr bt
  toEmpty    (BtITbl _ arr bt) = BtITbl EmptyOk  arr bt
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}






{-

instance
  ( Monad m
  , Element ls Subword -- (Z:.Subword:.Subword)
  , FirstSecond ls (arr (Z:.Subword:.Subword) x)
  , FirstSecondIdx ls (arr (Z:.Subword:.Subword) x) Subword
  , PrimArrayOps arr (Z:.Subword:.Subword) x
  , MkStream m ls Subword
  , Show x
  ) => MkStream m (ls :!: ITbl m arr (Z:.Subword:.Subword) x) Subword where
  mkStream (ls :!: ITbl _ _ c t elm) (IStatic ()) hh (Subword (i:.j))
    = map (\s -> let (Subword (_:.l)) = getIdx s
                     ab               = if greenLight ls t
                                          then greenIdx ls (undefined :: Subword) t s
                                          else subword 0 0
                 in  -- traceShow ("13",ab,subword l j,t!(Z:.ab:.subword l j)) $
                     ElmITbl (t ! (Z:.ab:.subword l j)) (subword l j) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - 0))
  mkStream (ls :!: ITbl _ _ c t elm) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - 0))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - 0)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                        ab             = if greenLight ls t
                                                           then greenIdx ls (undefined :: Subword) t s
                                                           else subword 0 0
                                    --traceShow ("02",ab,subword k l,t!(Z:.ab:.subword k l)) $
                                    return $ Yield (ElmITbl (t ! (Z:.ab:.kl)) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , FirstSecond ls (arr (Z:.Subword:.Subword) x)
  , FirstSecondIdx ls (arr (Z:.Subword:.Subword) x) Subword
  , PrimArrayOps arr (Z:.Subword:.Subword) x
  , Element ls Subword
  , MkStream mB ls Subword
  , Show r
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (Z:.Subword:.Subword) x) mF mB r) Subword where
  mkStream (ls :!: BtITbl c t bt) (IStatic ()) hh (Subword (i:.j))
    = mapM (\s -> let (Subword (_:.l)) = getIdx s
                      lj               = subword l j
                      light            = greenLight ls t
                      ab               = if light
                                           then greenIdx ls (undefined :: Subword) t s
                                           else lj -- subword 0 0
                      ablj             = if light
                                           then Z:.ab:.lj
                                           else Z:.subword 0 0:.subword 0 0 -- Z:.lj:.lj
                  in bt (Prelude.snd $ bounds t) ablj >>= \ ~bb -> {- traceShow (ab,lj,bb) $ -} return $ ElmBtITbl (t ! ablj) bb lj (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - 0))
  mkStream (ls :!: BtITbl c t bt) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - 0))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - 0)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                        light          = greenLight ls t
                                        ab             = if light
                                                           then greenIdx ls (undefined :: Subword) t s
                                                           else kl -- subword 0 0
                                        abkl           = if light
                                                           then Z:.ab:.kl
                                                           else Z:.subword 0 0:.subword 0 0 -- Z:.kl:.kl
                                    bt (Prelude.snd $ bounds t) abkl >>= \ ~bb -> {- traceShow (ab,kl,bb) $ -} return $ Yield (ElmBtITbl (t!abkl) bb kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

-}


{-

-- | Get the previous index; this should really be made generic!
--
-- TODO This is probably a REALLY STUPID IDEA ;-)

class FirstSecond x k where
  greenLight :: x -> k -> Bool

class FirstSecondIdx x k i where
  greenIdx :: x -> i -> k -> Elm x i -> Subword

instance FirstSecond S k where
  greenLight S _ = False
  {-# Inline greenLight #-}



instance
  ( FirstSecond ls (arr (Z:.Subword:.Subword) x)
  ) => FirstSecond (ls :!: ITbl m arr (Z:.Subword:.Subword) x) (arr (Z:.Subword:.Subword) x) where
  greenLight (ls :!: ITbl _ _ _ t _) t' =
    case reallyUnsafePtrEquality# t t' of
      -- TODO speaking of stupid ideas!
      1# -> True
      _  -> greenLight ls t'
  {-# Inline greenLight #-}

instance
  ( FirstSecond ls (arr (Z:.Subword:.Subword) x)
  ) => FirstSecond (ls :!: Backtrack (ITbl mF arr (Z:.Subword:.Subword) x) mF mB r) (arr (Z:.Subword:.Subword) x) where
  greenLight (ls :!: BtITbl _ t _) t' =
    case reallyUnsafePtrEquality# t t' of
      -- TODO speaking of stupid ideas!
      1# -> True
      _  -> greenLight ls t'
  {-# Inline greenLight #-}



instance FirstSecondIdx S k i where
  greenIdx S _ _ _ = error "shouldn't arrive here!"
  {-# Inline greenIdx #-}

instance
  ( FirstSecondIdx ls (arr (Z:.Subword:.Subword) x) Subword
  , Elm ls Subword ~ RecElm (ls :!: ITbl m arr (Z:.Subword:.Subword) x) Subword
  , Element ls Subword
  ) => FirstSecondIdx (ls :!: ITbl m arr (Z:.Subword:.Subword) x) (arr (Z:.Subword:.Subword) x) Subword where
  greenIdx (ls :!: ITbl _ _ _ t _) _ t' e =
    case reallyUnsafePtrEquality# t t' of
      1# -> let ab = getIdx e in ab
      _  -> let g = getElm e in greenIdx ls (undefined :: Subword) t' g
  {-# Inline greenIdx   #-}

instance
  ( FirstSecondIdx ls (arr (Z:.Subword:.Subword) x) Subword
  , Elm ls Subword ~ RecElm (ls :!: Backtrack (ITbl mF arr (Z:.Subword:.Subword) x) mF mB r) Subword
  , Element ls Subword
  ) => FirstSecondIdx (ls :!: Backtrack (ITbl mF arr (Z:.Subword:.Subword) x) mF mB r) (arr (Z:.Subword:.Subword) x) Subword where
  greenIdx (ls :!: BtITbl _ t _) _ t' e =
    case reallyUnsafePtrEquality# t t' of
      1# -> let ab = getIdx e in ab
      _  -> let g = getElm e in greenIdx ls (undefined :: Subword) t' g
  {-# Inline greenIdx   #-}

-}


