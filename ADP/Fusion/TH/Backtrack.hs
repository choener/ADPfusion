
-- | Backtracking which uses lists internally. The basic idea is to convert
-- each @Stream@ into a list. The consumer consumes the stream lazily, but
-- allows for fusion to happen. The hope is that this improves total
-- performance in those cases, where backtracking has significant costs.

module ADP.Fusion.TH.Backtrack where

import           Control.Monad
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
import           Data.Vector.Fusion.Stream.Monadic (Stream(..))
import           Debug.Trace

import           ADP.Fusion.TH.Common



-- | @Backtracking@ products of @f@ and @b@. Choice in @f@ needs to be
-- reduced to a scalar value. It is then compared to the @fst@ values
-- in @b@. From those, @choice b@ selects.

class ProductBacktracking sigF sigB where
  type SigBacktracking sigF sigB :: *
  (<||) :: sigF -> sigB -> SigBacktracking sigF sigB

-- | The ADP-established product operation. Returns a vector of results,
-- along the lines of what the ADP @f *** b@ provides.

class ProductCombining sigF sigB where
  type SigCombining sigF sigB :: *
  (***) :: sigF -> sigB -> SigCombining sigF sigB

-- | Creates instances for all products given a signature data type.

makeProductInstances :: Name -> Q [Dec]
makeProductInstances tyconName = do
  t <- reify tyconName
  case t of
    TyConI (DataD ctx tyConName args cs d) -> do
      let m = getMonadName args
      case cs of
        [RecC dataconName funs] -> do
          let Just (h,m',x,r) = getObjectiveNames funs
          mL <- newName "mL"
          xL <- newName "xL"
          rL <- newName "rL"
          mR <- newName "mR"
          xR <- newName "xR"
          rR <- newName "rR"
--          let lType    = buildLeftType  tyconName (m', x, r) (mL, xL)        args
          let lType    = buildRightType tyconName (m', x, r) (mL, xL, rL)    args
          let rType    = buildRightType tyconName (m', x, r) (mR, xR, rR)    args
          let (fs,hs) = partition ((`notElem` [h]) . sel1) funs
          let sigBType = buildSigBacktrackingType  tyconName (m', x, r) xL (mR, xR, rR) args
          Clause psB (NormalB bB) dsB <- genAlgProdFunctions buildBacktrackingChoice dataconName funs fs hs
          iB <- [d| instance (Monad $(varT mL), Monad $(varT mR), Eq $(varT xL), $(varT mL) ~ $(varT mR), $(varT xL) ~ $(varT rL))
                      => ProductBacktracking $(return lType) $(return rType) where
                          type SigBacktracking $(return lType) $(return rType) = $(return sigBType)
                          (<||) = $(return $ LamE psB $ LetE dsB bB)
                          {-# Inline (<||) #-}
                |]
          -- TODO might well be that this doesn't work because we re-use
          -- type names ...
          vG <- newName "vG"
          sigPType <- buildSigCombiningType tyconName vG (m', x, r) (mL, xL, rL) (mR, xR, rR) args
          Clause psC (NormalB bC) dsC <- genAlgProdFunctions buildCombiningChoice    dataconName funs fs hs
          iC <- [d| instance (Monad $(varT mL), Monad $(varT mR), Eq $(varT xL), $(varT mL) ~ $(varT mR) {- , VG.Vector $(varT vG) ($(varT rL),$(varT rR)) -} )
                      => ProductCombining $(return lType) $(return rType) where
                          type SigCombining $(return lType) $(return rType) = $(return sigPType)
                          (***) = undefined
                          {-
                           - (***) = $(return $ LamE psC $ LetE dsC bC)
                           - -}
                          {-# Inline (***) #-}
                |]
          return $ iB -- ++ iC

-- | Returns the 'Name' of the monad variable.

getMonadName :: [TyVarBndr] -> Maybe Name
getMonadName = go
  where go [] = Nothing
        go (KindedTV m (AppT (AppT ArrowT StarT) StarT) : _) = Just m
        go (_ : xs) = go xs

-- | Returns the 'Name's of the objective function variables, as well as
-- the name of the objective function itself.

getObjectiveNames :: [VarStrictType] -> Maybe (Name,Name,Name,Name)
getObjectiveNames = go
  where go [] = Nothing
        go ( (hName , _ , (AppT (AppT ArrowT (AppT (AppT (ConT streamName) (VarT mS)) (VarT x))) (AppT (VarT mR) (VarT r)))) : xs)
          | streamName == ''Stream && mS == mR = Just (hName,mS,x,r)
          | otherwise             = go xs
        go ( _ : xs) = go xs



-- * Constructions for the different algebra types.

-- | The left algebra type. Assumes that in @choice :: Stream m x -> m r@
-- we have that @x ~ r@.

buildLeftType :: Name -> (Name, Name, Name) -> (Name, Name) -> [TyVarBndr] -> Type
buildLeftType tycon (m, x, r) (mL, xL) = foldl AppT (ConT tycon) . map (VarT . go)
  where go (PlainTV z)
          | z == m        = mL  -- correct monad name
          | z == x        = xL  -- point to new x type
          | z == r        = xL  -- stream and return type are the same
          | otherwise     = z   -- everything else can stay as is
        go (KindedTV z _) = go (PlainTV z)

-- | Here, we do not set any restrictions on the types @m@ and @r@.

buildRightType :: Name -> (Name, Name, Name) -> (Name, Name, Name) -> [TyVarBndr] -> Type
buildRightType tycon (m, x, r) (mR, xR, rR) = foldl AppT (ConT tycon) . map (VarT . go)
  where go (PlainTV z)
          | z == m    = mR
          | z == x    = xR
          | z == r    = rR
          | otherwise = z
        go (KindedTV z _) = go (PlainTV z)

-- | Build up the type for backtracking. We want laziness in the right
-- return type. Hence, we have @AppT ListT (VarT xR)@.

buildSigBacktrackingType :: Name -> (Name, Name, Name) -> (Name) -> (Name, Name, Name) -> [TyVarBndr] -> Type
buildSigBacktrackingType tycon (m, x, r) (xL) (mR, xR, rR) = foldl AppT (ConT tycon) . map go
  where go (PlainTV z)
          | z == m    = VarT mR
          | z == x    = (AppT (AppT (TupleT 2) (VarT xL)) (AppT ListT (VarT xR)))
          | z == r    = VarT rR
          | otherwise = VarT z
        go (KindedTV z _) = go (PlainTV z)

-- | Build up the type for backtracking. We want laziness in the right
-- return type. Hence, we have @AppT ListT (VarT xR)@.

buildSigCombiningType :: Name -> Name -> (Name, Name, Name) -> (Name, Name, Name) -> (Name, Name, Name) -> [TyVarBndr] -> TypeQ
buildSigCombiningType tycon vG (m, x, r) (mL, xL, rL) (mR, xR, rR) = foldl appT (conT tycon) . map go
  where go (PlainTV z)
          | z == m    = varT mR
          | z == x    = [t| ($(varT xL) , $(varT xR)) |]
          | z == r    = [t| V.Vector ($(varT rL) , $(varT rR)) |]
          | otherwise = varT z
        go (KindedTV z _) = go (PlainTV z)



-- *

-- | Build up attribute and choice function.

genAlgProdFunctions
  :: Choice
  -> Name
  -> [VarStrictType]
  -> [VarStrictType]
  -> [VarStrictType]
  -> Q Clause
genAlgProdFunctions choice conName allFunNames evalFunNames choiceFunNames = do
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
          $  zipWith3 (genChoiceFunction choice) (drop (length evalFunNames) fnmsL) (drop (length evalFunNames) fnmsR) choiceFunNames
          ++ zipWith3 (genAttributeFunction nonTermNames) fnmsL fnmsR evalFunNames
  -- build the function pairs
  -- to keep our sanity, lets print this stuff
  let cls = Clause [varL, varR] (NormalB rce) [whereL,whereR]
  return cls

-- |

genChoiceFunction
  :: Choice
  -> Name
  -> Name
  -> VarStrictType
  -> Q (Name,Exp)
genChoiceFunction choice hL hR (name,_,t) = do
  exp <- choice hL hR
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

-- | Type for backtracking functions.
--
-- Not too interesting, mostly to keep track of @choice@.

type Choice = Name -> Name -> Q Exp

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

buildBacktrackingChoice :: Choice
buildBacktrackingChoice hL' hR' =
  [| \xs -> do        -- first, create a boxed, mutable vector from the results
               ysM <- streamToVector xs -- VGM.unstream xs :: m (VM.MVector s (t1,[t2]))
                      -- apply first choice
               hFres <- $(varE hL') $ SM.map fst $ vectorToStream ysM
                     -- second choice on snd elements, then concat'ed up
                     -- TODO good candidate for rewriting into flatten
                     -- operation!
               {-
                - $(varE hR') $ SM.concatMap (SM.fromList . snd) $ SM.filter ((hFres==) . fst) $ vectorToStream ysM
                -}
               $(varE hR') $ SM.fromList $ concatMap snd $ filter ((hFres==) . fst) $ V.toList ysM
  |]

buildCombiningChoice :: Choice
buildCombiningChoice hL' hR' =
  [| \xs -> do       -- first, create a boxed, mutable vector from the results
               --ys <- streamToVector xs
               --      -- apply first choice
               --fs <- $(varE hL') $ SM.map fst $ vectorToStream ys
               --      -- generate a vector of vectors, one for each
               --      -- surviving @f@
               --vs <- V.forM fs $ \f -> do
               --        -- keep only those @ys@ that have @f@
               --        let as = V.filter ((f==) . fst) ys
               --        -- apply @hR'@ to those, but only to the @snd@
               --        -- elements
               --        bs <- streamToVector =<< $(varE hR') $ SM.map snd $ vectorToStream $ as
               --        -- return the combined result, with @f@ attached.
               --        return $ V.map (\z -> (f,z)) bs
               undefined
               {-
                - $ V.concat $ V.toList vs
                -}
               -- TODO we should return a @newtype Many x = forall (G.Vector v x) => Many { v x }
               -- Together with a closed type family, this gives us a good
               -- way to encode that we have classified DP
  |]

-- | Transform a monadic stream monadically into a vector.
--
-- TODO Improve code!

streamToVector :: (Monad m) => SM.Stream m x -> m (V.Vector x)
streamToVector xs = do
  l <- SM.toList xs
  let v = V.fromList l
  return v
{-# Inline streamToVector #-}

-- | Transform a vector into a monadic stream.
--
-- TODO improve code!

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

