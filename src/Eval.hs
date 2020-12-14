module Eval (call, eval1, def2let, macroExpandExpr, macroExpandStmt) where

import Prelude.Extra

import Data.List (sortOn)
import qualified Data.Map.Strict as Map

import Env
import Parser
import Syntax

isExpr :: Stmt -> Bool
isExpr = \case
  Expr _ -> True
  Def _ _ -> False
  TypeDecl _ -> False
  MacroStmt _ _ -> error "shouldn't have macro here"

macroExpandStmt :: FullEnv -> Stmt -> Either Text Stmt
macroExpandStmt env stmt = case stmt of
  MacroStmt name trees -> do
    case Map.lookup name (feVars env) of
      Just (_, Macro (BuiltinMacro _ f)) -> do
        tree <- f trees
        treeToStmt env tree
      Just _ -> Left "Attempting to macroexpand a non-macro"
      Nothing -> Left "Attempting to macroexpand a nonexistent var"
  Expr te -> let (t, e) = extractType te
             in Expr . mkTyped t <$> macroExpandExpr env e
  _ -> return stmt

macroExpandExpr :: FullEnv -> Expr -> Either Text Expr
macroExpandExpr env expr = case expr of
  MacroExpr name trees -> do
    case Map.lookup name (feVars env) of
      Just (_, Macro (BuiltinMacro _ f)) -> do
        tree <- f trees
        treeToExpr env tree
      Just _ -> Left "Attempting to macroexpand a non-macro"
      Nothing -> Left "Attempting to macroexpand a nonexistent var"

  Val _ -> return expr
  Var _ -> return expr
  Let bs e -> Let <$> meBindings bs <*> meTyped e
  LetRec bs e -> LetRec <$> meBindings bs <*> meTyped e
  Lam n e -> Lam n <$> meTyped e
  Call e1 e2 -> Call <$> meTyped e1 <*> meTyped e2
  IfMatch inE pat thenE elseE ->
    IfMatch <$> meTyped inE <*> pure pat <*> meTyped thenE <*> meTyped elseE
 where
  meTyped te = let (t, e) = extractType te
               in mkTyped t <$> macroExpandExpr env e
  meBindings = traverse (\(n, e) -> (n,) <$> meTyped e)

def2let :: [Stmt] -> Either Text (Typed Expr)
def2let exprs = go [] $ sortOn isExpr exprs
 where
  go pairs = \case
   [] -> Left "need at least one expr"
   [Expr e] -> let (t, _) = extractType e in Right $ mkTyped t $ LetRec pairs e
   (Expr _) : _ -> Left $ "can only have one expr" <> tshow exprs
   (Def n1 e1) : e -> go ((n1, e1):pairs) e
   (TypeDecl _) : e -> go pairs e
   (MacroStmt _ _) : _ -> Left "Should have macroexpanded first"

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

  IfMatch inE pat thenE elseE -> do
    inV <- eval1 env (rmType inE)
    case patternMatch (rmType pat) inV of
      Nothing -> eval1 env (rmType elseE)
      Just bindings -> eval1 (Env $ Map.union (Map.fromList bindings) syms) (rmType thenE)

  -- Left is for program errors, this is a compiler error
  MacroExpr _ _ -> error "Should have macroexpanded first"
 where
  elimThunk :: Val -> Either Text Val
  elimThunk (Thunk newenv e) = elimThunk =<< eval1 newenv e
  elimThunk x = Right x

-- | If `val` matches `pat`, return Just a list of bound variables.
patternMatch :: Pattern -> Val -> Maybe [(Name, Val)]
patternMatch pat val = case pat of
  PatLiteral l -> case val of
    Literal l' | l == l' -> Just []
    _ -> Nothing
  PatVal n -> Just [(n, val)]
  PatConstr conName pats -> case val of
    Tag tName vals
      | tName == conName && length vals == length pats
      -> fmap concat $ sequence $ zipWith (patternMatch . rmType) pats vals
    _ -> Nothing

call :: Val -> Val -> Either Text Val
call (Builtin (Builtin' _ b)) a = b a
call (Clos (Env syms) param body) a = do
  let syms2 = Map.insert param a syms
  eval1 (Env syms2) body
call val _ = error $ "attempted to call non-closure " ++ show val
