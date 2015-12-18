
-- | @Chr@ on sets is equivalent to having a @Vertex@ symbol. Each bit
-- denotes one vertex point.

module ADP.Fusion.Term.Chr.Set0 where

import           Data.Proxy
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import           Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           Prelude hiding (map)
import           Data.Bits
import           Data.Bits.Extras (msb,Ranked)
import           Data.Bits.Ordered

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Chr.Type



instance
  ( TmkCtx1 m ls (Chr r x) (BitSet i)
  ) => MkStream m (ls :!: Chr r x) (BitSet i) where
  mkStream (ls :!: Chr f xs) sv us is
    = S.map (\(ss,ee,ii) -> ElmChr ee ii ss)
    . addTermStream1 (Chr f xs) sv us is
    $ mkStream ls (termStaticVar (Chr f xs) sv is) us (termStreamIndex (Chr f xs) sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx1 m ts a is (BitSet I)
  , Ranked (BitSet I)
  ) => TermStream m (TermSymbol ts (Chr r x)) a (is:.BitSet I) where
  termStream (ts:|Chr f xs) (cs:.IStatic rb) (us:.u) (is:.i)
    = staticCheck (rb <= popCount i && i <= u && VG.length xs > msb u)
    . S.flatten mk step . termStream ts cs us is
          -- we task all set bits @bs@ and also the index @i@ and calculate
          -- the non-set bits @mask@. The mask should have a popcount equal
          -- to @rb + 1@. We then active bit 0 and proceed with @step@.
    where mk svS = let RiBsI bs = getIndex (tIx svS) (Proxy :: PRI is (BitSet I))
                       mask = i `xor` bs
                   in  return (svS :. mask :. lsbZ mask)
          -- In case we can still do a step via @k>=0@, we active bit @k@
          -- in @aa@.
          step (svS@(TState s a ii ee) :. mask :. k )
            | k < 0 = return $ Done
            | otherwise =
            let RiBsI aa = getIndex a (Proxy :: PRI is (BitSet I))
            in  return $ Yield (TState s a (ii:.: RiBsI (setBit aa k)) (ee:.f xs k))
                               (svS :. mask :. nextActiveZ k mask)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

instance TermStaticVar (Chr r x) (BitSet I) where
  termStaticVar _ (IStatic   rb) _ = IStatic   $ rb + 1
  termStaticVar _ (IVariable rb) _ = IVariable $ rb + 1
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

