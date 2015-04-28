
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Backtracking which uses lists internally. The basic idea is to convert
-- each @Stream@ into a list. The consumer consumes the stream lazily, but
-- allows for fusion to happen. The hope is that this improves total
-- performance in those cases, where backtracking has significant costs.

module ADP.Fusion.TH.Backtrack where

import           Data.List
import           Data.Tuple.Select
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import           Control.Monad.Primitive (PrimState, PrimMonad)

import           ADP.Fusion.TH.Common



genClauseBacktrack
  :: Name
  -> [VarStrictType]
  -> [VarStrictType]
  -> [VarStrictType]
  -> Q Clause
genClauseBacktrack conName allFunNames evalFunNames choiceFunNames = do
  let nonTermNames = nub . map getRuleResultType $ evalFunNames
  -- bind the l'eft and r'ight variable of the two algebras we want to join,
  -- also create unique names for the function names we shall bind later.
  nameL <- newName "l"
  varL  <- varP nameL
  -- TODO automate discovery of choice functions?
  fnmsL <- sequence $ replicate (length allFunNames) (newName "fnamL")
  nameR <- newName "r"
  varR  <- varP nameR
  fnmsR <- sequence $ replicate (length allFunNames) (newName "fnamR")
  -- bind the individual variables in the where part
  whereL <- valD (conP conName (map varP fnmsL)) (normalB $ varE nameL) []
  whereR <- valD (conP conName (map varP fnmsR)) (normalB $ varE nameR) []
  rce <- recConE conName
          $  zipWith3 (genChoiceFunction) (drop (length evalFunNames) fnmsL) (drop (length evalFunNames) fnmsR) choiceFunNames
          ++ zipWith3 (genAttributeFunction nonTermNames) fnmsL fnmsR evalFunNames
  -- build the function pairs
  -- to keep our sanity, lets print this stuff
  let cls = Clause [varL, varR] (NormalB rce) [whereL,whereR]
  return cls

-- |

genChoiceFunction
  :: Name
  -> Name
  -> VarStrictType
  -> Q (Name,Exp)
genChoiceFunction hL hR (name,_,t) = do
  exp <- buildBacktrackingChoice hL hR
  return (name,exp)


-- |
--
-- TODO need fun names from @l@ and @r@

genAttributeFunction
  :: [Name]
  -> Name
  -> Name
  -> VarStrictType
  -> Q (Name,Exp)
genAttributeFunction nts fL fR (name,_,t) = do
  (lamPat,funL,funR) <-recBuildLamPat nts fL fR (init $ getRuleSynVarNames t) -- @init@ since we don't want the result as a parameter
  let exp = LamE lamPat $ TupE [funL,funR]
  return (name,exp)

-- |

recBuildLamPat :: [Name] -> Name -> Name -> [Name] -> Q ([Pat], Exp, Exp)
recBuildLamPat nts fL' fR' ts = do
  -- here we just run through all arguments, either creating an @x@ and
  -- a @ys@ for a non-term or a @t@ for a term.
  ps <- sequence [ if t `elem` nts then tupP [newName "x" >>= varP, newName "ys" >>= varP] else (newName "t" >>= varP) | t<-ts]
  let buildLfun f (TupP [VarP v,_]) = appE f (varE v)
      buildLfun f (VarP v         ) = appE f (varE v)
  lfun <- foldl buildLfun (varE fL') ps
  rfun <- buildRns (VarE fR') ps
  return (ps, lfun, rfun)


-- |
--
-- NOTE
--
-- @
-- [ f x | x <- xs ]
-- CompE [BindS (VarP x) (VarE xs), NoBindS (AppE (VarE f) (VarE x))]
-- @

buildRns
  :: Exp
--  -> [Name]
  -> [Pat]
  -> ExpQ
buildRns f ps = do
  ys <- sequence [ newName "y" | TupP [_,VarP v] <- ps ]
  let vs = zipWith (\y v -> (BindS (VarP y) (VarE v))) ys [ v | TupP [_,VarP v] <- ps ]
  let xs = go ps ys
  ff <- noBindS $ foldl (\g z -> appE g (varE z)) (return f) xs
  return $ CompE $ vs ++ [ff]
  where go [] [] = []
        go (VarP v : gs) ys     = v : go gs ys  -- keep terminal binders
        go (TupP _ : gs) (v:ys) = v : go gs ys  -- insert new binders
        go as bs = error $ show ("not done?", as, bs)

-- | Build up the backtracking choice function. This choice function will
-- backtrack based on the first result, then return only the second.
--
-- TODO it should be (only?) this function we will need to modify to build
-- all algebra products.
--
-- @ysM@ can't be unboxed, as @snd@ of each element is a list, lazily
-- consumed. We build up @ysM@ as this makes fusion happen. Of course, this
-- is a boxed vector and not as efficient, but we gain the ability to have
-- lazily created backtracking from this!
--
-- This means strict optimization AND lazy backtracking

buildBacktrackingChoice :: Name -> Name -> Q Exp
buildBacktrackingChoice hL' hR' =
  [| \xs -> do        -- first, create a boxed, mutable vector from the results
               ysM <- streamToVector xs -- VGM.unstream xs :: m (VM.MVector s (t1,[t2]))
                      -- apply first choice
               hFres <- $(varE hL') $ SM.map fst $ vectorToStream ysM
                     -- second choice on snd elements, then concat'ed up
                     -- TODO good candidate for rewriting into flatten
                     -- operation!
               $(varE hR') $ SM.concatMap (SM.fromList . snd) $ SM.filter ((hFres==) . fst) $ vectorToStream ysM
  |]

-- | Transform a monadic stream monadically into a vector.

streamToVector :: (Monad m) => SM.Stream m x -> m (V.Vector x)
streamToVector xs = do
  l <- SM.toList xs
  let v = V.fromList l
  return v
{-# Inline streamToVector #-}

-- | Transform a vector into a monadic stream.

vectorToStream :: (Monad m) => V.Vector x -> SM.Stream m x
vectorToStream = SM.fromList . V.toList
{-# Inline vectorToStream #-}

-- | Gets the names used in the evaluation function. This returns one
-- 'Name' for each variable.
--
-- In case of @TupleT 0@ the type is @()@ and there isn't a name to go with
-- it. We just @mkName "()"@ a name, but this might be slightly dangerous?
-- (Not really sure if it indeed is)
--
-- With @AppT _ _@ we have a multidim terminal and produce another hackish
-- name to be consumed above.
--
-- @
-- AppT (AppT ArrowT (AppT (AppT (ConT Data.Array.Repa.Index.:.) (AppT (AppT (ConT Data.Array.Repa.Index.:.) (ConT Data.Array.Repa.Index.Z)) (VarT c_1627675270))) (VarT c_1627675270))) (VarT x_1627675265)
-- @

getRuleSynVarNames :: Type -> [Name]
getRuleSynVarNames t' = go t' where
  go t
    | VarT x <- t = [x]
    | AppT (AppT ArrowT (VarT x  )) y <- t = x : go y   -- this is a syntactic variable, return the name that the incoming data is bound to
    | AppT (AppT ArrowT (AppT _ _)) y <- t = mkName "[]" : go y   -- this captures that we have a multi-dim terminal.
    | AppT (AppT ArrowT (TupleT 0)) y <- t = mkName "()" : go y   -- this case captures things like @nil :: () -> x@ for rules like @nil <<< Epsilon@.
    | otherwise            = error $ "getRuleSynVarNames error: " ++ show t ++ "    in:    " ++ show t'

