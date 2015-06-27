
module ADP.Fusion.SynVar.Array.TermSymbol where

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



-- | TODO need to deal with @minSize@

instance
  ( Monad m
  , TerminalStream m a is
  , PrimArrayOps arr Subword x
  ) => TerminalStream m (TermSymbol a (ITbl m arr Subword x)) (is:.Subword) where
  terminalStream (a :| ITbl _ _ c t _) (sv:.IStatic _) (is:.ix@(Subword (i:.j)))
    = map (\ (S6 s (zi:.(Subword (_:.l))) (zo:._) is os e) ->
              let lj = subword l j
              in  S6 s zi zo (is:.lj) (os:.subword 0 0) (e:.(t!lj)) )
    . iPackTerminalStream a sv (is:.ix)
  terminalStream (a :| ITbl _ _ c t _) (sv:.IVariable _) (is:.ix@(Subword (i:.j)))
    = flatten mk step Unknown . iPackTerminalStream a sv (is:.ix)
    where mk (S6 s (zi:.(Subword (_:.l))) (zo:._) is os e) = return (S6 s zi zo is os e :. l :. j - l) -- TODO minsize c !
          step (s6:.k:.z) | z >= 0 = do let S6 s zi zo is os e = s6
                                            l                  = j - z
                                            kl                 = subword k l
                                        return $ Yield (S6 s zi zo (is:.kl) (os:.subword 0 0) (e:.(t!kl))) (s6 :. k :. z-1)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline terminalStream #-}


{-
  mkStream (ls :!: ITbl _ _ c t _) (IVariable ()) hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmITbl (t ! kl) kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done

  terminalStream (a:|Chr f v) (sv:.IVariable _) (is:.ix@(Subword (i:.j)))
    = S.map (\(S6 s (zi:.Subword (_:.l)) (zo:._) is os e) -> S6 s zi zo (is:.subword l (l+1)) (os:.subword 0 0) (e:.f v l))
    . iPackTerminalStream a sv (is:.ix)
  {-# Inline terminalStream #-}

instance TermStaticVar (Chr r x) Subword where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (Subword (i:.j)) = subword i (j-1)
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

-}

