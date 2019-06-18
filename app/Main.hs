module Main where

import Prelude.Extra

import Control.Monad.Except (liftEither, runExceptT)
import qualified Data.Text.IO as Text
import qualified Options.Applicative as O
import Shower (printer)

import Eval
import Parser

data CmdLine = CmdLine
  { printTree :: Bool
  , printExpr :: Bool
  , noExec :: Bool
  , program :: String
  }

parser :: O.Parser CmdLine
parser = CmdLine
  <$> O.switch (O.long "print-tree" <> O.help "Print the syntax tree")
  <*> O.switch (O.long "print-expr" <> O.help "Print the parsed expressions")
  <*> O.switch (O.long "no-exec" <> O.help "Don't execute the program")
  <*> O.argument O.str (O.metavar "PROGRAM")

main :: IO ()
main = doCmdLine =<< O.execParser opts
 where
  opts = O.info (O.helper <*> parser)
    ( O.fullDesc <> O.progDesc "Run a program" )

doCmdLine :: CmdLine -> IO ()
doCmdLine (CmdLine {..}) = runExceptT go >>= \case
  Left err -> do
    putStrLn "failed"
    Text.putStrLn err
  Right Nothing -> return ()
  Right (Just res) -> print res
 where
  go = do
   trees <- liftEither $ parseWholeFile "<str>" program
   when printTree $ liftIO $ printer trees
   exprs <- liftEither $ treesToExprs trees
   when printExpr $ liftIO $ printer exprs
   if noExec
     then return Nothing
     else liftEither $ Just <$> eval defaultSymbols exprs
