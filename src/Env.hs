module Env
  ( FullEnv(..)
  , InferEnv(..)
  , TypeEnv(..)
  , declareTypes
  , getInferEnv
  , getSymbols
  ) where

import Prelude.Extra

import qualified Data.Map as Map
import Data.Map ((!?))

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

declareTypes :: [TypeDecl] -> FullEnv -> Either Text FullEnv
declareTypes decls env = foldM (flip declareType) env decls

declareType :: TypeDecl -> FullEnv -> Either Text FullEnv
declareType (TypeDecl' { tdName, tdConstructors }) env = do
  nv <- newVars
  nt <- newTypes
  return env { feVars = nv, feTypes = nt }
 where
  newMType = TCon $ TC HType tdName
  newPType = Forall [] newMType
  newTypes = return $ tInsert tdName newPType (feTypes env)
  newVars = foldM
    (\vars (conName, argNames) -> do
      ty <- conType argNames
      val <- conVal conName argNames
      return $ Map.insert conName (ty, val) vars
    )
    (feVars env) tdConstructors

  -- We'll need to do constructors after all types have been added
  conType :: [Name] -> Either Text (PType Tc)
  conType argNames = do
    types <- forM argNames $ \name -> do
      pt <- maybe (Left "no such type") return $ feVars env !? name
      case fst pt of
        Forall [] mt -> return mt
        Forall _ _ -> Left "shouldn't be any vars here"
    return $ Forall [] $ foldr (+->) newMType types

  conVal :: Name -> [Name] -> Either Text Val
  conVal conName [] = return $ Tag conName []
  conVal _ _ = Left "don't support constructor args yet"
