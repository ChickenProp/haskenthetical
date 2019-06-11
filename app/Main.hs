module Main where

import qualified Data.Text.IO as Text
import System.Environment (getArgs)

import Eval
import Syntax
import Parser
import Util

evalStr :: String -> Either Text Val
evalStr pgm = strToExprs pgm >>= eval defaultSymbols

main :: IO ()
main = do
  pgm <- head <$> getArgs
  case evalStr pgm of
    Left e -> do
      putStrLn "failed"
      Text.putStrLn e
    Right v -> print v
