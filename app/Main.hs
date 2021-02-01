module Main where

import Prelude.Extra

import Control.Monad.Except (liftEither, runExceptT)
import qualified Data.Text.IO as Text
import qualified GHC.IO.Encoding as Encoding
import qualified Options.Applicative as O
import Shower (printer)

import App
import Env
import Eval
import Syntax

data CmdLine = CmdLine
  { printConfig :: PrintingAppConfig
  , verbose :: Bool
  , noExec :: Bool
  , program :: Either String String
  }

parser :: O.Parser CmdLine
parser = CmdLine
  <$> (PrintingAppConfig
       <$> O.switch (O.long "print-tree" <> O.help "Print the syntax tree")
       <*> O.switch (O.long "print-expr"
                     <> O.help "Print the parsed expressions")
       <*> O.switch (O.long "print-expansion"
                     <> O.help "Print the macroexpansion")
       <*> O.switch (O.long "print-env" <> O.help "Print the environment")
       <*> O.switch (O.long "print-type" <> O.help "Print the inferred type")
      )
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
        then c { printConfig = PrintingAppConfig True True True True True }
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
  go = do
   (fName, src) <- case program of
     Left s -> return ("<-e>", s)
     Right s -> fmap (s,) $ liftIO $ readFile s

   (_, env, expr) <-
     liftEither . first ppCompileError
       =<< runPrintingAppT (compileProgram fName src) printConfig

   if noExec
     then return Nothing
     else liftEither $ Just <$> eval1 (getSymbols env) expr
