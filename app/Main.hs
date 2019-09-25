module Main where

import Prelude.Extra

import Control.Monad.Except (liftEither, runExceptT)
import qualified Data.Text.IO as Text
import qualified Options.Applicative as O
import Shower (printer)

import Defaults
import Eval
import Parser
import Syntax
import TypeCheck

data CmdLine = CmdLine
  { printTree :: Bool
  , printExpr :: Bool
  , printType :: Bool
  , verbose :: Bool
  , noExec :: Bool
  , program :: String
  }

parser :: O.Parser CmdLine
parser = CmdLine
  <$> O.switch (O.long "print-tree" <> O.help "Print the syntax tree")
  <*> O.switch (O.long "print-expr" <> O.help "Print the parsed expressions")
  <*> O.switch (O.long "print-type" <> O.help "Print the inferred type")
  <*> O.switch (O.long "verbose" <> O.short 'v' <> O.help "Print everything")
  <*> O.switch (O.long "no-exec" <> O.help "Don't execute the program")
  <*> O.argument O.str (O.metavar "PROGRAM")



main :: IO ()
main = do
  c <- O.execParser opts
  let c' = if verbose c
        then c { printTree = True, printExpr = True, printType = True }
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
  go = do
   trees <- liftEither $ parseWholeFile "<str>" program
   when printTree $ liftIO $ printer trees
   exprs <- liftEither $ treesToExprs trees
   when printExpr $ liftIO $ printer exprs
   expr1 <- liftEither $ def2let exprs
   ty <- liftEither $ runTypeCheck defaultTypes expr1
   when printType $ liftIO $ printer ty
   if noExec
     then return Nothing
     else liftEither $ Just <$> eval1 defaultSymbols (rmType expr1)
