module Env
  ( FullEnv(..)
  , InferEnv(..)
  , TypeEnv
  , declareMacs
  , declareTypes
  , declareVars
  , getInferEnv
  , getSymbols
  , me2tc_MType
  , me2tc_PType
  ) where

import Prelude.Extra

import Data.List ((\\))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Map.Strict ((!?))
import qualified Data.TreeDiff as TD

import Gist
import Syntax

type TypeEnv t = Map Name (t Tc)

data FullEnv = FullEnv
  { feVars :: Map Name (PType Tc, Val), feTypes :: TypeEnv MType }
  deriving (Show, Generic)

instance Gist FullEnv where
  gist (FullEnv{..}) =
    TD.Rec "FullEnv"
      $ Map.fromList [("feVars", gist feVars), ("feTypes", gist feTypes)]

data InferEnv = InferEnv { ieVars :: TypeEnv PType, ieTypes :: TypeEnv MType }
  deriving (Show, Generic)

getInferEnv :: FullEnv -> InferEnv
getInferEnv (FullEnv {feVars, feTypes}) =
  InferEnv {ieVars = fst <$> feVars, ieTypes = feTypes}

getSymbols :: FullEnv -> Env
getSymbols (FullEnv {feVars}) = Env $ snd <$> feVars

insertUnique :: Ord k => e -> k -> v -> Map k v -> Either e (Map k v)
insertUnique e k v orig = Map.alterF alter k orig
 where alter (Just _) = Left e
       alter Nothing = Right (Just v)

me2tc_MType :: TypeEnv MType -> MType Me -> Either CompileError (MType Tc)
me2tc_MType env = \case
  TCon (TC NoExt n) -> maybe (Left $ CEUnknownType n) return (env !? n)
  TVar (TV NoExt n) -> return $ TVar $ TV HType n
  TApp a b -> TApp <$> me2tc_MType env a <*> me2tc_MType env b
  MacroMType v _ _ -> absurd v

me2tc_PType :: TypeEnv PType -> PType Me -> Either CompileError (PType Tc)
me2tc_PType env = \case
  Forall [] (TCon (TC NoExt n)) -> do
   case env !? n of
     Nothing -> Left $ CEUnknownType n
     Just t -> return t
  Forall [] (TVar (TV NoExt n)) ->
    return $ Forall [TV HType n] (TVar $ TV HType n)
  Forall [] (a `TApp` b) -> do
    Forall vsl tl <- me2tc_PType env $ Forall [] a
    Forall vsr tr <- me2tc_PType env $ Forall [] b
    return $ Forall (vsl `Set.union` vsr) $ tl `TApp` tr
  Forall _ _ ->
    Left $ CECompilerBug
      "I don't know how to handle foralls in type annotations yet"
  MacroPType v _ _ -> absurd v

declareVars
  :: [(Name, PType Tc, Typed Tc (Expr Tc))]
  -> FullEnv
  -> Either CompileError FullEnv
declareVars [] env = return env
declareVars vars env = do
  let newNames = flip map vars $ \(name, _, _) -> name
      existingNames = Map.keys $ feVars env
  forM_ (group $ sort $ newNames ++ existingNames) $ \case
    [] -> error "impossible"
    [_] -> pure ()
    (x:_) -> Left $ CEMultiDeclareValue x

  let insertions = flip map vars $ \(name, ty, expr) ->
        (name, (ty, Thunk newSymbols $ rmType expr))
      newFeVars = feVars env <> Map.fromList insertions
      ret = env { feVars = newFeVars }
      newSymbols = getSymbols ret

  return ret

declareMacs :: [(Name, Expr Tc)] -> FullEnv -> Either CompileError FullEnv
declareMacs macs env = foldM go env macs
 where
  go env' (name, expr) = do
    -- Not env' because macros declared in the same block can't reference each
    -- other.
    let val = Macro $ Thunk (getSymbols env) expr
    newFeVars <-
      insertUnique (CEMultiDeclareValue name)
                   name
                   (Forall [] tMacro, val)
                   (feVars env')
    return env' { feVars = newFeVars }

declareTypes :: [TypeDecl Me] -> FullEnv -> Either CompileError FullEnv
declareTypes decls env = do
  -- We might have mutually recursive types, e.g.
  --
  --     (Type Foo (Foo Bar))
  --     (Type Bar (Bar Foo))
  --
  -- By declaring all the type constructors before any of the data constructors,
  -- this isn't a problem.
  env2 <- foldM (flip declareType) env decls
  env3 <- foldM (flip declareTypeConstructors) env2 decls
  foldM (flip declareTypeEliminator) env3 decls

declareType :: TypeDecl Me -> FullEnv -> Either CompileError FullEnv
declareType (TypeDecl' { tdName, tdVars }) env = do
  nt <- newTypes
  return env { feTypes = nt }
 where
  k = foldr (\_ a -> HType :*-> a) HType tdVars
  newMType = TCon $ TC k tdName
  newTypes = insertUnique (CEMultiDeclareType tdName)
                          tdName newMType (feTypes env)

declareTypeConstructors :: TypeDecl Me -> FullEnv -> Either CompileError FullEnv
declareTypeConstructors (TypeDecl' { tdName, tdVars, tdConstructors }) env = do
  nv <- newVars
  return env { feVars = nv }
 where
  k = foldr (\_ a -> HType :*-> a) HType tdVars
  newMType = TCon $ TC k tdName
  newVars = foldM
    (\vars (conName, argNames) -> do
      ty <- conType argNames
      let val = conVal conName argNames
      insertUnique (CEMultiDeclareConstructor conName) conName (ty, val) vars
    )
    (feVars env) tdConstructors

  conType :: [MType Me] -> Either CompileError (PType Tc)
  conType argNames = do
    types <- mapM (me2tc_MType (feTypes env)) argNames
    let allVars = map (TV HType) tdVars
        finalType = foldl' TApp newMType (Set.fromList $ TVar <$> allVars)

    -- Forbid constructors from using type variables not mentioned in
    -- `tdVars`. This would give us values with no attached types. E.g. after
    -- `(type X (X $y))`, `(X 3)` and `(X "foo")` are both valid expressions of
    -- type `X`.
    let usedVars = mapMaybe (\case { TVar x -> Just x; _ -> Nothing }) types
    case map getName usedVars \\ tdVars of
      [] -> return ()
      x:_ -> Left (CEUnknownType x) -- can only easily report one at a time

    return $ Forall (Set.fromList allVars) $ foldr (+->) finalType types

  conVal :: Name -> [MType Me] -> Val
  conVal conName ts = go [] 0 (length ts)
   where
    go :: [Val] -> Int -> Int -> Val
    go acc _ 0 = Tag conName acc
    go acc d n = mkBuiltinUnsafe $ do
      v <- getArg (mkName d)
      pure $ Right $ go (acc ++ [v]) (d + 1) (n - 1)

    mkName 0 = conName
    mkName n = conName <> "." <> Name (tshow n)

declareTypeEliminator :: TypeDecl Me -> FullEnv -> Either CompileError FullEnv
declareTypeEliminator (TypeDecl' { tdName, tdVars, tdConstructors }) env = do
  teType <- typeElimType
  newVars <- insertUnique (CEMultiDeclareValue typeElimName)
                          typeElimName (teType, typeElimVal) (feVars env)
  return env { feVars = newVars }
 where
  resultTVar :: TVar Tc
  resultTVar = TV HType "%a"
  resultType :: MType Tc
  resultType = TVar resultTVar

  valKind = foldr (\_ a -> HType :*-> a) HType tdVars
  allVars = TV HType <$> tdVars

  valType :: MType Tc
  valType = foldl' TApp
                   (TCon $ TC valKind tdName)
                   (Set.fromList $ TVar <$> allVars)

  conElimType :: [MType Me] -> Either CompileError (MType Tc)
  conElimType typesPs = do
    typesTc <- mapM (me2tc_MType $ feTypes env) typesPs
    return $ foldr (+->) resultType typesTc

  typeElimType :: Either CompileError (PType Tc)
  typeElimType = do
    mt <- foldr (+->) (valType +-> resultType)
            <$> mapM (conElimType . snd) tdConstructors
    return $ Forall (Set.fromList $ resultTVar : allVars) mt

  typeElimName :: Name
  typeElimName = "elim-" <> tdName

  applyConElim :: Val -> [Val] -> Either Text Val
  applyConElim f vals =
    Right
      $ Thunk (Env Map.empty)
      $ rmType
      $ foldl' (\e1 e2 -> UnTyped $ Call e1 e2)
               (UnTyped $ Val f)
               (UnTyped . Val <$> vals)

  typeElimVal :: Val
  typeElimVal = go [] 0 (fst <$> tdConstructors)
   where
    go :: [(Name, Val)] -> Int -> [Name] -> Val
    go acc _ [] = mkBuiltinUnsafe $ do
      v <- getArg (typeElimName <> ".fin")
      return $ case v of
        Tag n xs | Just f <- lookup n acc -> applyConElim f xs
        _ -> Left "Bad tag"
    go acc d (n : rest) = mkBuiltinUnsafe $ do
      f <- getArg (mkName d)
      return $ Right $ go (acc ++ [(n, f)]) (d+1) rest

    mkName 0 = typeElimName
    mkName n = typeElimName <> "." <> Name (tshow n)
