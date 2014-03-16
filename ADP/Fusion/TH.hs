{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}

-- | The functions in here auto-create suitable algebra product functions from
-- a signature. Currently, functions @<**@ are supported which have scalar
-- results in the first variable.
--
-- TODO If we want to support classified DP, we shall also need @**<@
-- generating vector-results given a vector result, followed by a scalar
-- result.
--
-- TODO Then we also need @***@ handling the case of vector-to-vector results.
--
-- TODO note the comments in @buildChoice@

module ADP.Fusion.TH where

import           Data.List
import           Data.Tuple.Select
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM


-- | Create the algebra product function from a signature type constructor.
--
-- TODO make the resulting function INLINE
--
-- TODO compare @ntTypes@ with the stream argument types of all @hs@ (via their
-- @hns@ names). If there is a mismatch, then either not all non-terminal types
-- have a corresponding choice function or vice versa.

makeAlgebraProductH :: [Name] -> Name -> Q [Dec]
makeAlgebraProductH hns nm = do
  rnm <- reify nm
  case rnm of
    TyConI (DataD ctx tyConName args cs d) -> case cs of
      -- we analyze the accessor functions and look for the objective function
      -- accessor. It's stream parameter is the type of the non-terminal.
      -- Everything else in accessors are terminal parameters.
      [RecC dataConName fs'] -> do
        -- split @fs@ into functions applied to rule RHSs and choice functions (@hs@)
        let (fs,hs) = partition ((`notElem` hns) . sel1) fs'
        -- the result types of the @fs@ are the types of the non-terminal symbols
        let ntTypes = nub . map getNtTypes $ fs
        fun <- funD (mkName "<**") [genClause dataConName fs' fs hs]
        return
          [ fun
          ]
      _   -> fail "more than one data ctor"
    _          -> fail "unsupported data type"

-- | Build the single clause of our function. We shall need the functions bound
-- in the where part to create the joined functions we need to return.

genClause conName allFunNames evalFunNames choiceFunNames = do
  let nonTermNames = nub . map getNtTypes $ evalFunNames
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
          ++ zipWith3 (genEvalFunction nonTermNames) fnmsL fnmsR evalFunNames
  -- build the function pairs
  -- to keep our sanity, lets print this stuff
  let cls = Clause [varL, varR] (NormalB rce) [whereL,whereR]
  return cls

genChoiceFunction hL hR (name,_,t) = do
  exp <- buildChoice hL hR
  return (name,exp)

-- |
--
-- TODO need fun names from @l@ and @r@

genEvalFunction nts fL fR (name,_,t) = do
  (lamPat,funL,funR) <-recBuildLamPat nts fL fR $ init $ getNames t -- @init@ since we don't want the result as a parameter
  let exp = LamE lamPat $ TupE [funL,funR]
  return (name,exp)

-- |

recBuildLamPat :: [Name] -> Name -> Name -> [[Name]] -> Q ([Pat], Exp, Exp)
recBuildLamPat nts fL' fR' ts = do
  ps <- sequence [ if length t==1 && head t `elem` nts then tupP [newName "x" >>= varP, newName "ys" >>= varP] else (newName "t" >>= varP) | t<-ts]
  let buildLfun f (TupP [VarP v,_]) = appE f (varE v)
      buildLfun f (VarP v         ) = appE f (varE v)
  lfun <- foldl buildLfun (varE fL') ps
  rfun <- buildRns (VarE fR') [] ps
  return (ps, lfun, rfun)

buildRns f xs []                     = appE ([| return . SM.singleton |]) (foldl (\g z -> appE g (varE z)) (return f) xs)
buildRns f xs (VarP v          : ys) = buildRns f (xs++[v]) ys
buildRns f xs (TupP [_,VarP v] : ys) = do w  <- newName "w"
                                          [| $(varE v) >>= return . SM.concatMapM $(lamE [varP w] (buildRns f (xs++[w]) ys)) |]

-- | Build up the choice function.
--
-- TODO it should be (only?) this function we will need to modify to build all
-- algebra products.

buildChoice :: Name -> Name -> Q Exp
buildChoice hL' hR' = do
  [| \xs -> do hfs <- $(varE hL') $ SM.map fst xs
               let phfs = SM.concatMapM snd . SM.filter ((hfs==) . fst) $ xs
               $(varE hR') phfs |]

-- | Gets the names used in the evaluation function.

getNames :: Type -> [[Name]]
getNames t = go t where
  go t
    | VarT x <- t = [[x]]
    | AppT (AppT ArrowT (VarT x  )) y <- t = [x] : go y
    | AppT (AppT ArrowT (AppT _ _)) y <- t = []  : go y  -- later on, grab all terminal names in a multi-dim case
    | otherwise            = error $ "getNames error: " ++ show t

-- AppT (AppT ArrowT (AppT (AppT (ConT Data.Array.Repa.Index.:.) (AppT (AppT (ConT Data.Array.Repa.Index.:.) (ConT Data.Array.Repa.Index.Z)) (VarT c_1627675270))) (VarT c_1627675270))) (VarT x_1627675265)

-- | Get us the 'Name' of a non-terminal type. Theses are simply the last
-- @VarT@s occuring in a function.

getNtTypes :: VarStrictType -> Name
getNtTypes vst = go $ sel3 vst where
  go t
    | AppT _ (VarT x) <- t = x
    | AppT _ x        <- t = go x
    | otherwise            = error $ "undetermined error:" ++ show vst

