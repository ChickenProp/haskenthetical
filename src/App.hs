module App
  ( AppMonad(..)
  , PrintingAppConfig(..)
  , PrintingAppT(..)
  , SilentApp(..)
  , compileProgram
  , compileProgramFromTrees
  ) where

import Prelude.Extra

import Control.Monad.Except (liftEither, runExceptT)
import Control.Monad.Trans (lift)
import Data.Either (partitionEithers)
import Shower (shower)

import Defaults
import Env
import Eval
import Gist
import Parser
import Syntax
import TypeCheck

data CompileStep
  = CSSyntaxTree
  | CSExpr
  | CSExpansion
  | CSEnvironment
  | CSType

class Monad m => AppMonad m where
  logStep :: CompileStep -> String -> m ()

logStepGist :: (AppMonad m, Gist a) => CompileStep -> a -> m ()
logStepGist step x = logStep step $ show $ prettyGist x <> "\n"

newtype SilentApp a = SilentApp { runSilentApp :: a }
  deriving stock (Eq, Show, Functor)
instance Applicative SilentApp where
  pure a = SilentApp a
  (SilentApp f) <*> (SilentApp x) = SilentApp $ f x
instance Monad SilentApp where
  (SilentApp x) >>= f = f x
instance AppMonad SilentApp where
  logStep _ _ = SilentApp ()

data PrintingAppConfig = PrintingAppConfig
  { printTree :: Bool
  , printExpr :: Bool
  , printExpansion :: Bool
  , printEnv :: Bool
  , printType :: Bool
  }

newtype PrintingAppT m a = PrintingAppT
  { runPrintingAppT :: PrintingAppConfig -> m a }
  deriving stock (Functor)
instance Applicative m => Applicative (PrintingAppT m) where
  pure a = PrintingAppT $ const $ pure a
  (PrintingAppT f) <*> (PrintingAppT x) =
    PrintingAppT $ \conf -> f conf <*> x conf
instance Monad m => Monad (PrintingAppT m) where
  (PrintingAppT x) >>= f =
    PrintingAppT $ \conf -> do
      x' <- x conf
      runPrintingAppT (f x') conf
instance MonadIO m => AppMonad (PrintingAppT m) where
  logStep step str = PrintingAppT $ \PrintingAppConfig{..} ->
    liftIO $ case step of
      CSSyntaxTree  -> when printTree $ putStrLn str
      CSExpr        -> when printExpr $ putStrLn str
      CSExpansion   -> when printExpansion $ putStrLn str
      CSEnvironment -> when printEnv $ putStrLn str
      CSType        -> when printType $ putStrLn str

compileProgram
  :: AppMonad m
  => String -> String -> m (Either CompileError (PType Tc, FullEnv, Expr Tc))
compileProgram fName src = runExceptT $ do
  trees <- liftEither $ parseWholeFile fName src
  lift $ logStep CSSyntaxTree $ shower trees
  ret <- lift $ compileProgramFromTrees trees
  liftEither ret

compileProgramFromTrees
  :: AppMonad m
  => [SyntaxTree] -> m (Either CompileError (PType Tc, FullEnv, Expr Tc))
compileProgramFromTrees trees = runExceptT $ do
  let topLevel = map treeToTopLevel trees
      (declGroups, otherTopLevel) =
        partitionEithers $ flip map topLevel $ \case
          DeclarationsPs _ ts -> Left ts
          OtherTopLevelPs _ t -> Right t
          Declarations v _ -> absurd v
          TopLevelDecl v _ -> absurd v
          TopLevelExpr v _ -> absurd v
      updateEnv env stmtTrees = do
        stmts <- liftEither $ treesToStmts env stmtTrees
        lift $ logStepGist CSExpr stmts

        expanded <- liftEither $ traverse (macroExpandStmt env) stmts
        lift $ logStepGist CSExpansion expanded

        let catMaybes3 (a, b, c) = (catMaybes a, catMaybes b, catMaybes c)
            (tyDecls, varDecls, macDecls) =
              catMaybes3 $ unzip3 $ flip map expanded $ \case
                TypeDecl d      -> (Just d, Nothing, Nothing)
                Def n e         -> (Nothing, Just (n, e), Nothing)
                DefMacro n e    -> (Nothing, Nothing, Just (n, e))
                Expr _          -> (Nothing, Nothing, Nothing)
                MacroStmt v _ _ -> absurd v

        newEnv1 <- liftEither $ declareTypes tyDecls env

        varDeclsTC <- liftEither $ typeCheckDefs (getInferEnv newEnv1) varDecls
        newEnv2 <- liftEither $ declareVars varDeclsTC newEnv1

        macDeclsTC <- liftEither $ typeCheckMacs (getInferEnv newEnv2) macDecls
        newEnv <- liftEither $ declareMacs macDeclsTC newEnv2

        lift $ logStepGist CSEnvironment newEnv
        return (expanded, newEnv)

  newEnv1 <- foldM (\e ts -> snd <$> updateEnv e ts) defaultEnv declGroups
  (expanded, newEnv) <- updateEnv newEnv1 otherTopLevel

  expr1 <- liftEither $ getOnlyExpr expanded
  (ty, tcExpr1) <- liftEither $ runTypeCheck (getInferEnv newEnv) expr1
  lift $ logStepGist CSType ty
  return (ty, newEnv, rmType tcExpr1)
