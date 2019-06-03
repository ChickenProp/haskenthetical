module Eval (eval, defaultSymbols) where

import Control.Monad (forM)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)

import Syntax

type SymbolTable = Map Name Val

hplus :: Val -> Either Text Val
hplus (Float a) = Right $ Builtin $ Builtin' "+.1" $ hplus1 a
hplus _ = Left "+ only accepts floats"

hplus1 :: Double -> Val -> Either Text Val
hplus1 a (Float b) = Right $ Float (a + b)
hplus1 _ _ = Left "+ takes exactly two arguments"

defaultSymbols :: SymbolTable
defaultSymbols = Map.fromList
  [ ("+", Builtin $ Builtin' "+" hplus)
  , ("three", Float 3)
  ]

eval :: SymbolTable -> [Expr] -> Either Text Val
eval _ [] = Left "need at least one expr"
eval syms [e] = eval1 syms e
eval _ _ = Left "unsupported"

eval1 :: SymbolTable -> Expr -> Either Text Val
eval1 syms (Val x) = Right x
eval1 syms (Var x) = case Map.lookup x syms of
  Nothing -> Left "no such var"
  Just v -> Right v
eval1 syms (Call f args) = do
  vf <- eval1 syms f
  vargs <- mapM (eval1 syms) args
  call syms vf vargs
eval1 _ _ = Left "unsupported expr"

call :: SymbolTable -> Val -> [Val] -> Either Text Val
call _ v [] = Right v
call syms (Builtin (Builtin' _ b)) (a:as) = b a >>= \next -> call syms next as
call syms (Lam param body) (a:as) = do
  let syms2 = Map.insert param a syms
  res1 <- eval1 syms2 body
  call syms2 res1 as
