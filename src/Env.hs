module Env
  ( FullEnv(..)
  , InferEnv(..)
  , TypeEnv
  , declareTypes
  , getInferEnv
  , getSymbols
  , ps2tc_PType
  ) where

import Prelude.Extra

import Data.List ((\\))
import qualified Data.Map as Map
import Data.Map ((!?))

import Syntax

type TypeEnv t = Map Name (t Tc)

data FullEnv = FullEnv
  { feVars :: Map Name (PType Tc, Val), feTypes :: TypeEnv MType }
  deriving (Show, Generic)

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

ps2tc_MType :: TypeEnv MType -> MType Ps -> Either CompileError (MType Tc)
ps2tc_MType env = \case
  TCon (TC NoExt n) -> maybe (Left $ CEUnknownType n) return (env !? n)
  TVar (TV NoExt n) -> return $ TVar $ TV HType n
  TApp a b -> TApp <$> ps2tc_MType env a <*> ps2tc_MType env b

ps2tc_PType :: TypeEnv PType -> PType Ps -> Either CompileError (PType Tc)
ps2tc_PType env = \case
  Forall [] (TCon (TC NoExt n)) -> do
   case env !? n of
     Nothing -> Left $ CEUnknownType n
     Just t -> return t
  Forall [] (TVar _) ->
    Left $ CECompilerBug
      "I don't know how to handle vars in type annotations yet"
  Forall [] (a `TApp` b) -> do
    tl <- ps2tc_PType env $ Forall [] a
    tr <- ps2tc_PType env $ Forall [] b
    case (tl, tr) of
      (Forall [] tl', Forall [] tr') -> do
        return $ Forall [] $ tl' `TApp` tr'
      _ -> Left $ CECompilerBug "Somehow got a Forall from `ps2tc_PType`?"
  Forall _ _ ->
    Left $ CECompilerBug
      "I don't know how to handle foralls in type annotations yet"

declareTypes :: [TypeDecl] -> FullEnv -> Either CompileError FullEnv
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

declareType :: TypeDecl -> FullEnv -> Either CompileError FullEnv
declareType (TypeDecl' { tdName, tdVars }) env = do
  nt <- newTypes
  return env { feTypes = nt }
 where
  k = foldr (\_ a -> HType :*-> a) HType tdVars
  newMType = TCon $ TC k tdName
  newTypes = insertUnique (CEMultiDeclareType tdName)
                          tdName newMType (feTypes env)

declareTypeConstructors :: TypeDecl -> FullEnv -> Either CompileError FullEnv
declareTypeConstructors (TypeDecl' { tdName, tdVars, tdConstructors }) env = do
  nv <- newVars
  return env { feVars = nv }
 where
  k = foldr (\_ a -> HType :*-> a) HType tdVars
  newMType = TCon $ TC k tdName
  newVars = foldM
    (\vars (conName, argNames) -> do
      ty <- conType argNames
      val <- conVal conName argNames
      insertUnique (CEMultiDeclareConstructor conName) conName (ty, val) vars
    )
    (feVars env) tdConstructors

  conType :: [MType Ps] -> Either CompileError (PType Tc)
  conType argNames = do
    types <- mapM (ps2tc_MType (feTypes env)) argNames
    let allVars = map (TV HType) tdVars
        finalType = foldl' TApp newMType (TVar <$> allVars)

    -- Forbid constructors from using type variables not mentioned in
    -- `tdVars`. This would give us values with no attached types. E.g. after
    -- `(type X (X $y))`, `(X 3)` and `(X "foo")` are both valid expressions of
    -- type `X`.
    let usedVars = mapMaybe (\case { TVar x -> Just x; _ -> Nothing }) types
    case map getName usedVars \\ tdVars of
      [] -> return ()
      x:_ -> Left (CEUnknownType x) -- can only easily report one at a time

    return $ Forall allVars $ foldr (+->) finalType types

  conVal :: Name -> [MType Ps] -> Either CompileError Val
  conVal conName ts = return $ go [] 0 (length ts)
   where
    go :: [Val] -> Int -> Int -> Val
    go acc _ 0 = Tag conName acc
    go acc d n = Builtin $ Builtin' (mkName d) $ \v ->
      Right $ go (acc ++ [v]) (d + 1) (n - 1)

    mkName 0 = conName
    mkName n = conName <> "." <> Name (tshow n)

declareTypeEliminator :: TypeDecl -> FullEnv -> Either CompileError FullEnv
declareTypeEliminator (TypeDecl' { tdName, tdVars, tdConstructors }) env = do
  teType <- typeElimType
  teVal <- typeElimVal
  newVars <- insertUnique (CEMultiDeclareValue typeElimName)
                          typeElimName (teType, teVal) (feVars env)
  return env { feVars = newVars }
 where
  resultType :: MType Tc
  resultType = TVar (TV HType "%a")

  valKind = foldr (\_ a -> HType :*-> a) HType tdVars
  allVars = TV HType <$> tdVars

  valType :: MType Tc
  valType = foldl' TApp (TCon $ TC valKind tdName) (TVar <$> allVars)

  conElimType :: [MType Ps] -> Either CompileError (MType Tc)
  conElimType typesPs = do
    typesTc <- mapM (ps2tc_MType $ feTypes env) typesPs
    return $ foldr (+->) resultType typesTc

  typeElimType :: Either CompileError (PType Tc)
  typeElimType = do
    mt <- foldr (+->) (valType +-> resultType)
            <$> mapM (conElimType . snd) tdConstructors
    return $ Forall allVars mt

  typeElimName :: Name
  typeElimName = "elim-" <> tdName

  applyConElim :: Val -> [Val] -> Either Text Val
  applyConElim f vals =
    Right $ Thunk (Env Map.empty) $ foldl' Call (Val f) (Val <$> vals)

  typeElimVal :: Either CompileError Val
  typeElimVal = case tdConstructors of
    [] -> error "unhandled"
    [(name, _)] -> Right $ Builtin $ Builtin' name $ \f1 ->
      Right $ Builtin $ Builtin' name $ \case
        Tag n xs | n == name -> applyConElim f1 xs
        _ -> Left "Bad tag"
    [(n1, _), (n2, _)] -> Right $ Builtin $ Builtin' n1 $ \f1 ->
      Right $ Builtin $ Builtin' n1 $ \f2 ->
        Right $ Builtin $ Builtin' n1 $ \case
          Tag n xs | n == n1 -> applyConElim f1 xs
          Tag n xs | n == n2 -> applyConElim f2 xs
          _ -> Left "Bad tag"
    [(n1, _), (n2, _), (n3, _)] -> Right $ Builtin $ Builtin' n1 $ \f1 ->
      Right $ Builtin $ Builtin' n1 $ \f2 ->
        Right $ Builtin $ Builtin' n1 $ \f3 ->
          Right $ Builtin $ Builtin' n1 $ \case
            Tag n xs | n == n1 -> applyConElim f1 xs
            Tag n xs | n == n2 -> applyConElim f2 xs
            Tag n xs | n == n3 -> applyConElim f3 xs
            _ -> Left "Bad tag"
    _ -> error "unhandled"
