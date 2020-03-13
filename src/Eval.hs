module Eval (call, eval1, def2let) where

import Prelude.Extra

import Data.List (sortOn)
import qualified Data.Map.Strict as Map

import Syntax

isStatement :: Expr -> Bool
isStatement = \case
  Val _ -> False
  Var _ -> False
  Let _ _ -> False
  LetRec _ _ -> False
  Lam _ _ -> False
  Call _ _ -> False
  Def _ _ -> True
  TypeDecl _ -> True

def2let :: [Typed Expr] -> Either Text (Typed Expr)
def2let exprs = go [] $ sortOn (not . isStatement . snd) $ map extractType exprs
 where
  go pairs = \case
   [] -> Left "need at least an expr"
   [(_, Def _ _)] -> Left "need an expr"
   [(t, e)] -> Right $ mkTyped t $ LetRec pairs e
   (_, Def n1 e1) : e -> go ((n1, e1):pairs) e
   (_, TypeDecl _) : e -> go pairs e
   _ -> Left $ "can only have one expr" <> tshow exprs

eval1 :: Env -> Expr -> Either Text Val
eval1 env@(Env syms) = elimThunk <=< \case
  Val x -> Right x

  Var x -> case Map.lookup x syms of
    Nothing -> Left $ "no such var: " <> tshow x
    Just v -> Right v

  Let [] expr -> eval1 env expr
  Let ((n, e):bs) expr -> do
    v <- eval1 env e
    eval1 (Env $ Map.insert n v syms) (Let bs expr)

  LetRec bindings expr -> do
    let thunks = flip map bindings $ \(n, e) -> (n, Thunk newenv e)
        newenv = Env $ Map.union (Map.fromList thunks) syms
    eval1 newenv expr

  Lam name expr -> Right $ Clos env name expr

  Call f arg -> do
    vf <- eval1 env f
    varg <- eval1 env arg
    call vf varg

  Def _ _ -> Left "Def should have been handled"
  TypeDecl _ -> Left "TypeDecl should have been handled"
 where
  elimThunk :: Val -> Either Text Val
  elimThunk (Thunk newenv e) = elimThunk =<< eval1 newenv e
  elimThunk x = Right x

call :: Val -> Val -> Either Text Val
call (Builtin (Builtin' _ b)) a = b a
call (Clos (Env syms) param body) a = do
  let syms2 = Map.insert param a syms
  eval1 (Env syms2) body
call val _ = error $ "attempted to call non-closure " ++ show val
