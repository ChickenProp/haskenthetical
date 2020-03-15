module Main where

import Prelude.Extra

import Control.Monad.Except (liftEither, runExceptT)
import qualified Data.Text.IO as Text
import qualified Options.Applicative as O
import Shower (printer)

import Defaults
import Env
import Eval
import Gist
import Parser
import Syntax
import TypeCheck

data CmdLine = CmdLine
  { printTree :: Bool
  , printExpr :: Bool
  , printEnv :: Bool
  , printType :: Bool
  , verbose :: Bool
  , noExec :: Bool
  , program :: String
  }

parser :: O.Parser CmdLine
parser = CmdLine
  <$> O.switch (O.long "print-tree" <> O.help "Print the syntax tree")
  <*> O.switch (O.long "print-expr" <> O.help "Print the parsed expressions")
  <*> O.switch (O.long "print-env" <> O.help "Print the environment")
  <*> O.switch (O.long "print-type" <> O.help "Print the inferred type")
  <*> O.switch (O.long "verbose" <> O.short 'v' <> O.help "Print everything")
  <*> O.switch (O.long "no-exec" <> O.help "Don't execute the program")
  <*> O.argument O.str (O.metavar "PROGRAM")



main :: IO ()
main = do
  c <- O.execParser opts
  let c' = if verbose c
        then c { printTree = True
               , printExpr = True
               , printEnv = True
               , printType = True
               }
        else c
  doCmdLine c'
 where
  opts = O.info (O.helper <*> parser)
    ( O.fullDesc <> O.progDesc "Run a program" )

doCmdLine :: CmdLine -> IO ()
doCmdLine (CmdLine {..}) = runExceptT go >>= \case
  Left err -> do
    putStrLn "failed"
    Text.putStrLn err
  Right Nothing -> return ()
  Right (Just res) -> printer res
 where
  printGist v = liftIO $ print $ prettyGist v <> "\n"
  go = do
   trees <- liftEither $ first tshow $ parseWholeFile "<str>" program
   when printTree $ liftIO $ printer trees
   stmts <- liftEither $ first tshow $ treesToStmts trees
   when printExpr $ printGist stmts

   let decls = flip mapMaybe (rmType <$> stmts) $ \case
         TypeDecl d -> Just d
         _ -> Nothing
   newEnv <- liftEither $ first tshow $ declareTypes decls defaultEnv
   when printEnv $ printGist newEnv

   expr1 <- liftEither $ def2let stmts
   ty <- liftEither $ first tshow $ runTypeCheck (getInferEnv newEnv) expr1
   when printType $ printGist ty
   if noExec
     then return Nothing
     else liftEither $ Just <$> eval1 (getSymbols newEnv) (rmType expr1)
