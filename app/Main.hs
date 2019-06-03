module Main where

import Eval
import Syntax

ast :: [Expr]
-- ast = [ Val $ Float 3 ]
ast = [ Call (Var "+") [Var "three", Call (Var "+") [Val $ Float 3, Val $ Float 5]]]

main :: IO ()
main = print (eval defaultSymbols ast)
