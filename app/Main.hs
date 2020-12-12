module Main where

import Prelude.Extra

import Control.Monad.Except (ExceptT, liftEither, runExceptT)
import qualified Data.Text.IO as Text
import qualified GHC.IO.Encoding as Encoding
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
  , program :: Either String String
  }

parser :: O.Parser CmdLine
parser = CmdLine
  <$> O.switch (O.long "print-tree" <> O.help "Print the syntax tree")
  <*> O.switch (O.long "print-expr" <> O.help "Print the parsed expressions")
  <*> O.switch (O.long "print-env" <> O.help "Print the environment")
  <*> O.switch (O.long "print-type" <> O.help "Print the inferred type")
  <*> O.switch (O.long "verbose" <> O.short 'v' <> O.help "Print everything")
  <*> O.switch (O.long "no-exec" <> O.help "Don't execute the program")
  <*> (Left <$> O.strOption
        (O.long "eval" <> O.short 'e' <> O.help "Evaluate from command line")
      <|> Right <$> O.argument O.str (O.metavar "PROGRAM")
      )

main :: IO ()
main = do
  -- We require that a .hth file is encoded in UTF-8 regardless of system
  -- settings. This affects String and Text IO.
  Encoding.setLocaleEncoding Encoding.utf8

  -- Not sure if we want this. It's the encoding used for argv and file paths.
  -- If I set `LC_ALL="en_US.iso88591"` then this makes `-e` work, but plausibly
  -- there are systems that do encode argv in something other than UTF-8 and
  -- which correctly say so. For now, trusting the system to be configured
  -- correctly.
  -- Encoding.setFileSystemEncoding Encoding.utf8

  -- Not sure if we want this either. It might affect FFI if we do that in
  -- future? Not including it for now.
  -- Encoding.setForeignEncoding Encoding.utf8

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
  Left err -> Text.putStrLn err
  Right Nothing -> return ()
  Right (Just res) -> printer res
 where
  printGist v = liftIO $ print $ prettyGist v <> "\n"

  liftCE :: Monad m => Either CompileError a -> ExceptT Text m a
  liftCE = liftEither . first ppCompileError

  go = do
   (fName, src) <- case program of
     Left s -> return ("<-e>", s)
     Right s -> fmap (s,) $ liftIO $ readFile s
   trees <- liftCE $ parseWholeFile fName src
   when printTree $ liftIO $ printer trees
   stmts <- liftCE $ treesToStmts trees
   when printExpr $ printGist stmts

   let decls = flip mapMaybe stmts $ \case
         TypeDecl d -> Just d
         _ -> Nothing
   newEnv <- liftCE $ declareTypes decls defaultEnv
   when printEnv $ printGist newEnv

   expr1 <- liftEither $ def2let stmts
   ty <- liftCE $ runTypeCheck (getInferEnv newEnv) expr1
   when printType $ printGist ty
   if noExec
     then return Nothing
     else liftEither $ Just <$> eval1 (getSymbols newEnv) (rmType expr1)
