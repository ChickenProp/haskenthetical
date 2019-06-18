module Eval (eval, defaultSymbols) where

import Prelude.Extra

import qualified Data.Map.Strict as Map

import Syntax

hplus :: Val -> Either Text Val
hplus (Float a) = Right $ Builtin $ Builtin' "+.1" $ hplus1 a
hplus _ = Left "+ only accepts floats"

hplus1 :: Double -> Val -> Either Text Val
hplus1 a (Float b) = Right $ Float (a + b)
hplus1 _ _ = Left "+ takes exactly two arguments"

defaultSymbols :: Env
defaultSymbols = Env $ Map.fromList
  [ ("+", Builtin $ Builtin' "+" hplus)
  , ("three", Float 3)
  ]

eval :: Env -> [Expr] -> Either Text Val
eval _ [] = Left "need at least one expr"
eval syms [e] = eval1 syms e
eval _ _ = Left "unsupported"


eval1 :: Env -> Expr -> Either Text Val
eval1 env (Val x) = Right $ case x of
  Lam name expr -> Clos env name expr
  _ -> x

eval1 (Env syms) (Var x) = case Map.lookup x syms of
  Nothing -> Left $ "no such var: " <> tshow x
  Just v -> Right v

eval1 env (Let [] expr) = eval1 env expr
eval1 env@(Env syms) (Let ((n, e):bs) expr) = do
  v <- eval1 env e
  eval1 (Env $ Map.insert n v syms) (Let bs expr)

eval1 env (Call f args) = do
  vf <- eval1 env f
  vargs <- mapM (eval1 env) args
  call env vf vargs

eval1 _ _ = Left "unsupported expr"


call :: Env -> Val -> [Val] -> Either Text Val
call _ v [] = Right v
call env (Builtin (Builtin' _ b)) (a:as) = b a >>= \next -> call env next as
call _ (Clos (Env syms) param body) (a:as) = do
  let syms2 = Map.insert param a syms
  res1 <- eval1 (Env syms2) body
  call (Env syms2) res1 as
call _ val _ = error $ "attempted to call non-closure " ++ show val
