module Eval (call, eval1, def2let) where

import Prelude.Extra

import Data.List (sortOn)
import qualified Data.Map.Strict as Map

import Syntax

isExpr :: Stmt -> Bool
isExpr = \case
  Expr _ -> True
  Def _ _ -> False
  TypeDecl _ -> False

def2let :: [Stmt] -> Either Text (Typed Expr)
def2let exprs = go [] $ sortOn isExpr exprs
 where
  go pairs = \case
   [] -> Left "need at least one expr"
   [Expr e] -> let (t, _) = extractType e in Right $ mkTyped t $ LetRec pairs e
   (Expr _) : _ -> Left $ "can only have one expr" <> tshow exprs
   (Def n1 e1) : e -> go ((UnTyped n1, UnTyped e1):pairs) e
   (TypeDecl _) : e -> go pairs e

eval1 :: Env -> Expr -> Either Text Val
eval1 env@(Env syms) = elimThunk <=< \case
  Val x -> Right x

  Var x -> case Map.lookup x syms of
    Nothing -> Left $ "no such var: " <> tshow x
    Just v -> Right v

  Let [] expr -> eval1 env (rmType expr)
  Let ((n, e):bs) expr -> do
    v <- eval1 env (rmType e)
    eval1 (Env $ Map.insert (rmType n) v syms) (Let bs expr)

  LetRec bindings expr -> do
    let thunks = flip map bindings $
          \(n, e) -> (rmType n, Thunk newenv (rmType e))
        newenv = Env $ Map.union (Map.fromList thunks) syms
    eval1 newenv (rmType expr)

  Lam name expr -> Right $ Clos env (rmType name) (rmType expr)

  Call f arg -> do
    vf <- eval1 env (rmType f)
    varg <- eval1 env (rmType arg)
    call vf varg
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
