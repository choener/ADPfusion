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



-- * Parse a single character.

data Chr x = Chr !(VU.Vector x)

chr = Chr
{-# INLINE chr #-}

instance Build (Chr x)

instance
  ( VU.Unbox x
  , StaticStack ls Subword
  ) => StaticStack (ls :!: Chr x) Subword where
  staticStack   (ls :!: _) =
    let (a :!: Subword (i:.j  ) :!: b            ) = staticStack ls
    in  (a :!: Subword (i:.j+1) :!: (max 0 $ b-1))
  staticExtends (ls :!: Chr xs)
    | Nothing <- se = Just $ subword 0 (VU.length xs)
    | Just sw <- se = Just sw
    where se = staticExtends ls
  {-# INLINE staticStack #-}
  {-# INLINE staticExtends #-}

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
  mkStream !(ls :!: Chr xs) (Inner cnc) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmChr s (VU.unsafeIndex xs l) (subword l $ l+1)
            )
    $ mkStream ls (Inner cnc) (subword i $ j-1)
  {-# INLINE mkStream #-}



-- * Peeking to the left

data PeekL x = PeekL !(VU.Vector x)

peekL = PeekL
{-# INLINE peekL #-}

instance Build (PeekL x)

instance
  ( VU.Unbox x
  , StaticStack ls Subword
  ) => StaticStack (ls :!: PeekL x) Subword where
  staticStack (ls :!: _) =
    let (a   :!: ij :!: b) = staticStack ls
    in  (a+1 :!: ij :!: b)
  staticExtends (ls :!: PeekL xs)
    | Nothing <- se = Just $ subword 0 (VU.length xs)
    | Just sw <- se = Just sw
    where se = staticExtends ls
  {-# INLINE staticStack #-}
  {-# INLINE staticExtends #-}

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
    in  dta `seq` S.map (\s -> ElmPeekL s dta (subword (j-1) j)) $ mkStream ls Outer ij
  mkStream !(ls :!: PeekL xs) (Inner cnc) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmPeekL s (VU.unsafeIndex xs l) (subword l l)
            )
    $ mkStream ls (Inner cnc) ij
  {-# INLINE mkStream #-}


-- | TODO replace with PeekL PeekR combinators

{-

data GChr x e = GChr !(VU.Vector x)

instance Build (GChr x e)

class GChrExtract x e where
  type GChrRet x e :: *
  gChrChk :: GChr x e -> Int -> Bool
  gChrGet :: GChr x e -> Int -> GChrRet x e

data GChrDef

instance (VUM.Unbox x) => GChrExtract x GChrDef where
  type GChrRet x GChrDef = x
  gChrChk _ !k = True
  gChrGet !(GChr xs) !k = VU.unsafeIndex xs k
  {-# INLINE gChrChk #-}
  {-# INLINE gChrGet #-}

gchr :: VU.Unbox e => VU.Vector e -> GChr e GChrDef
gchr !xs = GChr xs
{-# INLINE gchr #-}

data PeekL

instance (VUM.Unbox x) => GChrExtract x PeekL where
  type GChrRet x PeekL = (x :!: x)
  gChrChk _ !k = k>0
  gChrGet !(GChr xs) !k = (VU.unsafeIndex xs (k-1) :!: VU.unsafeIndex xs k)
  {-# INLINE gChrChk #-}
  {-# INLINE gChrGet #-}

chrL :: VU.Unbox e => VU.Vector e -> GChr e PeekL
chrL !xs = GChr xs
{-# INLINE chrL #-}

data PeekR

instance (VUM.Unbox x) => GChrExtract x PeekR where
  type GChrRet x PeekR = (x:!:x)
  gChrChk !(GChr xs) !k = k+1 < VU.length xs
  gChrGet !(GChr xs) !k = (VU.unsafeIndex xs k :!: VU.unsafeIndex xs (k+1))
  {-# INLINE gChrChk #-}
  {-# INLINE gChrGet #-}

chrR :: VU.Unbox e => VU.Vector e -> GChr e PeekR
chrR !xs = GChr xs
{-# INLINE chrR #-}



instance
  ( Elms ls Subword
  ) => Elms (ls :!: GChr e r) Subword where
  data Elm (ls :!: GChr e r) Subword = ElmGChr !(Elm ls Subword) !(GChrRet e r) !Subword
  type Arg (ls :!: GChr e r) = Arg ls :. (GChrRet e r)
  getArg !(ElmGChr ls x _) = getArg ls :. x
  getIdx !(ElmGChr _ _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- | Currently using the 'outerCheck' function, need to test if this really works well! (benchmark!)

instance
  ( Monad m
  , VU.Unbox x
  , GChrExtract x e
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: GChr x e) Subword where
  mkStream !(ls :!: gchr) Outer !ij@(Subword(i:.j))
    = let dta = gChrGet gchr $ j-1
      in  dta `seq` S.map (\s -> ElmGChr s dta (subword (j-1) j))
--                    $ S.filter (\s -> gChrChk gchr (j-1-942))           -- NOTE the actual leq check is performed outside of the loop, but branching still occurs in the loop
                    $ outerCheck (gChrChk gchr (j-942))
                    $ mkStream ls Outer (subword i $ j-1)
  mkStream !(ls :!: gchr) (Inner cnc) !ij@(Subword(i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s
                   in  ElmGChr s (gChrGet gchr $ l) (subword l $ l+1))
    $ S.filter (\s -> let (Subword (k:.l)) = getIdx s
                      in  gChrChk gchr $ l)
    $ mkStream ls (Inner cnc) (subword i $ j-1)
  {-# INLINE mkStream #-}

-}

