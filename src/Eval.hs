module Eval (call, eval) where

import Prelude.Extra

import qualified Data.Map.Strict as Map

import Syntax

eval :: Env -> [Expr] -> Either Text Val
eval _ [] = Left "need at least one expr"
eval syms [e] = eval1 syms e
eval _ _ = Left "unsupported"

eval1 :: Env -> Expr -> Either Text Val
eval1 env@(Env syms) = \case
  Val x -> Right x

  Var x -> case Map.lookup x syms of
    Nothing -> Left $ "no such var: " <> tshow x
    Just v -> Right v

  Let [] expr -> eval1 env expr
  Let ((n, e):bs) expr -> do
    v <- eval1 env e
    eval1 (Env $ Map.insert n v syms) (Let bs expr)

  Lam name expr -> Right $ Clos env name expr

  Call f arg -> do
    vf <- eval1 env f
    varg <- eval1 env arg
    call vf varg

  _ -> Left "unsupported expr"

call :: Val -> Val -> Either Text Val
call (Builtin (Builtin' _ b)) a = b a
call (Clos (Env syms) param body) a = do
  let syms2 = Map.insert param a syms
  eval1 (Env syms2) body
call val _ = error $ "attempted to call non-closure " ++ show val
