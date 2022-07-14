
-- | Build a backtracking function which uses @Stream@s internally.
-- Efficient fusion of these streams requires @HERMIT@! For most
-- backtracking cases, this is less of a problem since the backtracking
-- running time is much less than the forward case requires.

module ADPfusion.Core.TH.Stream where

import           Data.List
import           Data.Tuple.Select
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM

import           ADPfusion.Core.TH.Common



-- | Build the single clause of our function. We shall need the functions bound
-- in the where part to create the joined functions we need to return.

genClauseStream
  :: Name
  -> [VarStrictType]
  -> [VarStrictType]
  -> [VarStrictType]
  -> Q Clause
genClauseStream conName allFunNames evalFunNames choiceFunNames = do
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
  rfun <- buildRns (VarE fR') [] ps
  return (ps, lfun, rfun)


-- |

buildRns
  :: Exp
  -> [Name]
  -> [Pat]
  -> ExpQ
buildRns f xs []                     = appE ([| return . SM.singleton |]) (foldl (\g z -> appE g (varE z)) (return f) xs)
buildRns f xs (VarP v          : ys) = buildRns f (xs++[v]) ys
buildRns f xs (TupP [_,VarP v] : ys) = do w  <- newName "w"
                                          [| $(varE v) >>= return . SM.concatMapM $(lamE [varP w] (buildRns f (xs++[w]) ys)) |]

-- | Build up the backtracking choice function. This choice function will
-- backtrack based on the first result, then return only the second.
--
-- TODO it should be (only?) this function we will need to modify to build all
-- algebra products.

buildBacktrackingChoice :: Name -> Name -> Q Exp
buildBacktrackingChoice hL' hR' = do
  [| \xs -> do hfs <- $(varE hL') $ SM.map fst xs
               let phfs = SM.concatMapM snd . SM.filter ((hfs==) . fst) $ xs
               $(varE hR') phfs |]


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


