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

hcons :: Val -> Either Text Val
hcons v = Right $ Builtin $ Builtin' "cons.1" $ hcons1 v

hcons1 :: Val -> Val -> Either Text Val
hcons1 v1 v2 = Right $ v1 :* v2

hcar :: Val -> Either Text Val
hcar (a :* _) = Right a
hcar _ = Left "car only accepts pairs"

hcdr :: Val -> Either Text Val
hcdr (_ :* b) = Right b
hcdr _ = Left "cdr only accepts pairs"

heither :: Val -> Either Text Val
heither l = Right $ Builtin $ Builtin' "either.1" $ heither1 l

heither1 :: Val -> Val -> Either Text Val
heither1 l r = Right $ Builtin $ Builtin' "either.2" $ heither2 l r

heither2 :: Val -> Val -> Val -> Either Text Val
heither2 l _ (HLeft v) = call l v
heither2 _ r (HRight v) = call r v
heither2 _ _ _ = Left "final argument of either must be an Either"

defaultSymbols :: Env
defaultSymbols = Env $ Map.fromList
  [ ("+", Builtin $ Builtin' "+" hplus)
  , ("three", Float 3)
  , (",", Builtin $ Builtin' "," hcons)
  , ("car", Builtin $ Builtin' "," hcar)
  , ("cdr", Builtin $ Builtin' "," hcdr)
  , ("Left", Builtin $ Builtin' "Left" (Right . HLeft))
  , ("Right", Builtin $ Builtin' "Right" (Right . HRight))
  , ("either", Builtin $ Builtin' "either" heither)
  ]

eval :: Env -> [Expr] -> Either Text Val
eval _ [] = Left "need at least one expr"
eval syms [e] = eval1 syms e
eval _ _ = Left "unsupported"


eval1 :: Env -> Expr -> Either Text Val
eval1 _ (Val x) = Right x

eval1 (Env syms) (Var x) = case Map.lookup x syms of
  Nothing -> Left $ "no such var: " <> tshow x
  Just v -> Right v

eval1 env (Let [] expr) = eval1 env expr
eval1 env@(Env syms) (Let ((n, e):bs) expr) = do
  v <- eval1 env e
  eval1 (Env $ Map.insert n v syms) (Let bs expr)

eval1 env (Lam name expr) = Right $ Clos env name expr

eval1 env (Call f arg) = do
  vf <- eval1 env f
  varg <- eval1 env arg
  call vf varg

eval1 _ _ = Left "unsupported expr"


call :: Val -> Val -> Either Text Val
call (Builtin (Builtin' _ b)) a = b a
call (Clos (Env syms) param body) a = do
  let syms2 = Map.insert param a syms
  eval1 (Env syms2) body
call val _ = error $ "attempted to call non-closure " ++ show val
