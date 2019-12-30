module Env
  ( FullEnv(..)
  , InferEnv(..)
  , TypeEnv(..)
  , declareTypes
  , getInferEnv
  , getSymbols
  , ps2tc_PType
  ) where

import Prelude.Extra

import qualified Data.Map as Map

import Syntax

newtype TypeEnv = TypeEnv { _unTypeEnv :: Map Name (PType Tc) } deriving (Show)

data FullEnv = FullEnv
  { feVars :: Map Name (PType Tc, Val), feTypes :: TypeEnv }
  deriving (Show, Generic)

data InferEnv = InferEnv { ieVars :: TypeEnv, ieTypes :: TypeEnv }
  deriving (Show, Generic)

getInferEnv :: FullEnv -> InferEnv
getInferEnv (FullEnv {feVars, feTypes}) =
  InferEnv {ieVars = TypeEnv $ fst <$> feVars, ieTypes = feTypes}

getSymbols :: FullEnv -> Env
getSymbols (FullEnv {feVars}) = Env $ snd <$> feVars

tInsert :: Name -> PType Tc -> TypeEnv -> TypeEnv
tInsert n t (TypeEnv m) = TypeEnv $ Map.insert n t m

tLookup :: Name -> TypeEnv -> Maybe (PType Tc)
tLookup n (TypeEnv m) = Map.lookup n m

ps2tc_PType :: TypeEnv -> PType Ps -> Either Text (PType Tc)
ps2tc_PType env = \case
  Forall [] (TCon (TC NoExt n)) -> do
   case tLookup n env of
     Nothing -> Left $ "unknown type " <> tshow n
     Just t -> return t
  Forall [] (TVar _) ->
    Left "I don't know how to handle vars in type annotations yet"
  Forall [] (a `TApp` b) -> do
    tl <- ps2tc_PType env $ Forall [] a
    tr <- ps2tc_PType env $ Forall [] b
    case (tl, tr) of
      (Forall [] tl', Forall [] tr') -> do
        return $ Forall [] $ tl' `TApp` tr'
      _ -> Left "Somehow got a Forall from `ps2tc_PType`?"
  Forall _ _ ->
    Left "I don't know how to handle foralls in type annotations yet"

declareTypes :: [TypeDecl] -> FullEnv -> Either Text FullEnv
declareTypes decls env = do
  -- We might have mutually recursive types, e.g.
  --
  --     (Type Foo (Foo Bar))
  --     (Type Bar (Bar Foo))
  --
  -- By declaring all the type constructors before any of the data constructors,
  -- this isn't a problem.
  env2 <- foldM (flip declareType) env decls
  foldM (flip declareTypeConstructors) env2 decls

declareType :: TypeDecl -> FullEnv -> Either Text FullEnv
declareType (TypeDecl' { tdName }) env = do
  nt <- newTypes
  return env { feTypes = nt }
 where
  newPType = Forall [] $ TCon $ TC HType tdName
  newTypes = return $ tInsert tdName newPType (feTypes env)

declareTypeConstructors :: TypeDecl -> FullEnv -> Either Text FullEnv
declareTypeConstructors (TypeDecl' { tdName, tdConstructors }) env = do
  nv <- newVars
  return env { feVars = nv }
 where
  newMType = TCon $ TC HType tdName
  newVars = foldM
    (\vars (conName, argNames) -> do
      ty <- conType argNames
      val <- conVal conName argNames
      return $ Map.insert conName (ty, val) vars
    )
    (feVars env) tdConstructors

  conType :: [MType Ps] -> Either Text (PType Tc)
  conType argNames = do
    types <- forM argNames $ \name -> do
      pt <- ps2tc_PType (feTypes env) (Forall [] name)
      case pt of
        Forall [] mt -> return mt
        Forall _ _ -> Left "shouldn't be any vars here"
    return $ Forall [] $ foldr (+->) newMType types

  conVal :: Name -> [MType Ps] -> Either Text Val
  conVal conName ts = go [] 0 (length ts)
   where
    go :: [Val] -> Int -> Int -> Either Text Val
    go acc _ 0 = return $ Tag conName acc
    go acc d n = return $ Builtin $ Builtin' (mkName d) $ \v ->
      go (acc ++ [v]) (d + 1) (n - 1)

    mkName 0 = conName
    mkName n = conName <> "." <> Name (tshow n)
