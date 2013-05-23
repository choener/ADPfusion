{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Chr where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Data.Strict.Maybe
import Prelude hiding (Maybe(..))

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Classes



-- | Parses a single character.

chr xs = GChr (VU.unsafeIndex) xs
{-# INLINE chr #-}

-- | Parses a single character and returns the character to the left in a
-- strict Maybe.

chrLeft xs = GChr f xs where
  f xs k = ( if k>=1 then (Just $ VU.unsafeIndex xs (k-1)) else Nothing
           , VU.unsafeIndex xs k
           )
  {-# INLINE f #-}
{-# INLINE chrLeft #-}

-- | Parses a single character and returns the character to the right in a
-- strict Maybe.

chrRight xs = GChr f xs where
  f xs k = ( VU.unsafeIndex xs k
           , if k+1<VU.length xs then (Just $ VU.unsafeIndex xs (k+1)) else Nothing
           )
  {-# INLINE f #-}
{-# INLINE chrRight #-}

-- | A generic Character parser that reads a single character but allows
-- passing additional information.

data GChr r x = GChr !(VU.Vector x -> Int -> r) !(VU.Vector x)

instance Build (GChr r x)

instance
  ( ValidIndex ls Subword
  , VU.Unbox x
  ) => ValidIndex (ls :!: GChr r x) Subword where
    validIndex (ls :!: GChr _ xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
      i>=a && j<VU.length xs -c && i+b<=j && validIndex ls abc ij
    {-# INLINE validIndex #-}
    getParserRange (ls :!: GChr _ _) ix = let (a:!:b:!:c) = getParserRange ls ix in (a:!:b+1:!:max 0 (c-1))
    {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: GChr r x) Subword where
    data Elm (ls :!: GChr r x) Subword = ElmGChr !(Elm ls Subword) !r !Subword
    type Arg (ls :!: GChr r x) = Arg ls :. r
    getArg !(ElmGChr ls x _) = getArg ls :. x
    getIdx !(ElmGChr _ _ idx) = idx
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: GChr r x) Subword where
  mkStream !(ls :!: GChr f xs) Outer !ij@(Subword (i:.j)) =
    let dta = f xs (j-1)
    in  dta `seq` S.map (\s -> ElmGChr s dta (subword (j-1) j)) $ mkStream ls Outer (subword i $ j-1)
  mkStream !(ls :!: GChr f xs) (Inner cnc szd) !ij@(Subword (i:.j))
    = S.map (\s -> let Subword (k:.l) = getIdx s
                   in  ElmGChr s (f xs l) (subword l $ l+1)
            )
    $ mkStream ls (Inner cnc szd) (subword i $ j-1)
  {-# INLINE mkStream #-}





{-
-- * Parse a single character.

data Chr x = Chr !(VU.Vector x)

--chr = Chr
--{-# INLINE chr #-}

instance
  ( ValidIndex ls Subword
  , VU.Unbox xs
  ) => ValidIndex (ls :!: Chr xs) Subword where
    validIndex (ls :!: Chr xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
      let
      in  i>=a && j<VU.length xs -c && i+b<=j && validIndex ls abc ij
    {-# INLINE validIndex #-}
    getParserRange (ls :!: Chr xs) ix = let (a:!:b:!:c) = getParserRange ls ix in (a:!:b+1:!:max 0 (c-1))
    {-# INLINE getParserRange #-}

instance Build (Chr x)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Chr x) Subword where
  data Elm (ls :!: Chr x) Subword = ElmChr !(Elm ls Subword) !x !Subword
  type Arg (ls :!: Chr x) = Arg ls :. x
  getArg !(ElmChr ls x _) = getArg ls :. x
  getIdx !(ElmChr _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- |
--
-- For 'Outer' cases, we extract the data, 'seq' it and then stream. This moves
-- extraction out of the loop.

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Chr x) Subword where
  mkStream !(ls :!: Chr xs) Outer !ij@(Subword(i:.j)) =
    let dta = VU.unsafeIndex xs (j-1)
    in  dta `seq` S.map (\s -> ElmChr s dta (subword (j-1) j)) $ mkStream ls Outer (subword i $ j-1)
  mkStream !(ls :!: Chr xs) (Inner cnc szd) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmChr s (VU.unsafeIndex xs l) (subword l $ l+1)
            )
    $ mkStream ls (Inner cnc szd) (subword i $ j-1)
  {-# INLINE mkStream #-}
-}



-- * Peeking to the left

data PeekL x = PeekL !(VU.Vector x)

peekL = PeekL
{-# INLINE peekL #-}

instance Build (PeekL x)

instance
  ( ValidIndex ls Subword
  , VU.Unbox x
  ) => ValidIndex (ls :!: PeekL x) Subword where
  validIndex (ls :!: PeekL xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    i>=a && j<VU.length xs -c && i+b<=j && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: PeekL xs) ix = let (a:!:b:!:c) = getParserRange ls ix in (a+1:!:b:!:c)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: PeekL x) Subword where
  data Elm (ls :!: PeekL x) Subword = ElmPeekL !(Elm ls Subword) !x !Subword
  type Arg (ls :!: PeekL x) = Arg ls :. x
  getArg !(ElmPeekL ls x _) = getArg ls :. x
  getIdx !(ElmPeekL _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: PeekL x) Subword where
  mkStream !(ls :!: PeekL xs) Outer !ij@(Subword(i:.j)) =
    let dta = VU.unsafeIndex xs (j-1)
    in  dta `seq` S.map (\s -> ElmPeekL s dta (subword j j)) $ mkStream ls Outer ij
  mkStream !(ls :!: PeekL xs) (Inner cnc szd) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmPeekL s (VU.unsafeIndex xs $ l-1) (subword l l)
            )
    $ mkStream ls (Inner cnc szd) ij
  {-# INLINE mkStream #-}



-- * Peeking to the right

data PeekR x = PeekR !(VU.Vector x)

peekR = PeekR
{-# INLINE peekR #-}

instance Build (PeekR x)

instance
  ( ValidIndex ls Subword
  , VU.Unbox x
  ) => ValidIndex (ls :!: PeekR x) Subword where
  validIndex (ls :!: PeekR xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    i>=a && j<VU.length xs -c && i+b<=j && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: PeekR xs) ix = let (a:!:b:!:c) = getParserRange ls ix in (a:!:b:!:c+1)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: PeekR x) Subword where
  data Elm (ls :!: PeekR x) Subword = ElmPeekR !(Elm ls Subword) !x !Subword
  type Arg (ls :!: PeekR x) = Arg ls :. x
  getArg !(ElmPeekR ls x _) = getArg ls :. x
  getIdx !(ElmPeekR _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: PeekR x) Subword where
  mkStream !(ls :!: PeekR xs) Outer !ij@(Subword(i:.j)) =
    let dta = VU.unsafeIndex xs j
    in  dta `seq` S.map (\s -> ElmPeekR s dta (subword j j)) $ mkStream ls Outer ij
  mkStream !(ls :!: PeekR xs) (Inner cnc szd) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmPeekR s (VU.unsafeIndex xs l) (subword l l)
            )
    $ mkStream ls (Inner cnc szd) ij
  {-# INLINE mkStream #-}

