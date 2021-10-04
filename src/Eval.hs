{-# LANGUAGE UndecidableInstances #-}

module Eval
  ( call
  , eval1
  , getOnlyExpr
  , MacroExpand(..)
  , MacroExpandSafe(..)
  , syntaxTreeToVal
  , valToSyntaxTrees
  ) where

import Prelude.Extra

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Env
import Parser
import Syntax

class MacroExpand ps me | ps -> me, me -> ps where
  macroExpand :: FullEnv -> ps -> Either CompileError me
  default macroExpand
    :: MacroExpandSafe ps me => FullEnv -> ps -> Either CompileError me
  macroExpand _ = Right . macroExpandSafe

class MacroExpandSafe ps me | ps -> me, me -> ps where
  macroExpandSafe :: ps -> me

instance MacroExpand (Stmt Ps) (Stmt Me) where
  macroExpand env = \case
    MacroStmt NoExt name trees -> doExpandMacro treeToStmt env name trees
    Expr te -> Expr <$> macroExpand env te
    Def n te ->
      Def <$> macroExpand env n <*> macroExpand env te
    DefMacro n te -> DefMacro n <$> macroExpand env te
    TypeDecl td -> return $ TypeDecl $ macroExpandSafe td

-- | Needs UndecidableInstances because GHC doesn't use the context to know that
-- ps and me satisfy the fundeps.
instance MacroExpand ps me => MacroExpand (Typed Ps ps) (Typed Me me) where
  macroExpand env = \case
    UnTyped x -> UnTyped <$> macroExpand env x
    Typed t x -> Typed <$> macroExpand env t <*> macroExpand env x

instance MacroExpandSafe (MType Ps) (MType Me) where
  macroExpandSafe = \case
    TVar (TV NoExt n) -> TVar (TV NoExt n)
    TCon (TC NoExt n) -> TCon (TC NoExt n)
    TApp v1 v2 -> TApp (macroExpandSafe v1) (macroExpandSafe v2)

instance MacroExpand (PType Ps) (PType Me) where
  macroExpand env = \case
    Forall vars ty ->
      return $ Forall (Set.map expVar vars) (macroExpandSafe ty)
    MacroPType NoExt name args -> doExpandMacro parsePType env name args
    where expVar (TV NoExt n) = TV NoExt n

instance MacroExpandSafe Name Name where
  macroExpandSafe = id
instance MacroExpand Name Name

instance MacroExpand (Pattern Ps) (Pattern Me) where
  macroExpand env = \case
    PatConstr n pats -> PatConstr n <$> mapM (macroExpand env) pats
    PatVal n -> return $ PatVal n
    PatLiteral l -> return $ PatLiteral l

instance MacroExpand (Expr Ps) (Expr Me) where
  macroExpand env = \case
    MacroExpr NoExt name trees -> doExpandMacro treeToExpr env name trees
    Val       v  -> return $ Val v
    Var       v  -> return $ Var v
    Let    bs e  -> Let <$> meBindings bs <*> me e
    LetRec bs e  -> LetRec <$> meBindings bs <*> me e
    Lam    n  e  -> Lam <$> me n <*> me e
    Call   e1 e2 -> Call <$> me e1 <*> me e2
    IfMatch inE pat thenE elseE ->
      IfMatch <$> me inE <*> me pat <*> me thenE <*> me elseE
   where
    me :: MacroExpand ps me => ps -> Either CompileError me
    me = macroExpand env
    meBindings = traverse $ \(n, e) -> (,) <$> me n <*> me e

instance MacroExpandSafe (TypeDecl Ps) (TypeDecl Me) where
  macroExpandSafe (TypeDecl' {..}) =
    TypeDecl' {tdConstructors = newConstructors, ..}
    where newConstructors = flip map tdConstructors $ \(name, types) ->
            (name, macroExpandSafe <$> types)

syntaxTreeToVal :: SyntaxTree -> Val
syntaxTreeToVal = \case
  STString x -> Tag "STString" [Literal $ String x]
  STFloat x  -> Tag "STFloat" [Literal $ Float x]
  STBare x   -> Tag "STBare" [Literal $ String x]
  STTree xs  -> Tag "STTree" [syntaxTreesToVal xs]

syntaxTreesToVal :: [SyntaxTree] -> Val
syntaxTreesToVal = \case
  [] -> Tag "Nil" []
  t:ts -> Tag "Cons" [syntaxTreeToVal t, syntaxTreesToVal ts]

valToSyntaxTree :: Val -> Either Text SyntaxTree
valToSyntaxTree = elimThunk >=> \case
  Tag "STString" [Literal (String x)] -> Right $ STString x
  Tag "STFloat"  [Literal (Float x)]  -> Right $ STFloat x
  Tag "STBare"   [Literal (String x)] -> Right $ STBare x
  Tag "STTree"   [listVal]            -> STTree <$> valToSyntaxTrees listVal
  _ -> Left "Lifting an incorrect type: SyntaxTree"

valToSyntaxTrees :: Val -> Either Text [SyntaxTree]
valToSyntaxTrees = \case
  Tag "Nil" [] -> Right []
  Tag "Cons" [hd, tl] -> (:) <$> valToSyntaxTree hd <*> valToSyntaxTrees tl
  _ -> Left "Lifting an incorrect type: List SyntaxTree"

doExpandMacro
  :: MacroExpand (a Ps) (a Me)
  => (FullEnv -> SyntaxTree -> Either Text (a Ps))
  -> FullEnv
  -> Name
  -> [SyntaxTree]
  -> Either CompileError (a Me)
doExpandMacro parseTree env macName args = do
  case Map.lookup macName (feVars env) of
    Just (_, Macro func) -> do
      treeVal <- first CEMiscError $ call func $ syntaxTreesToVal args
      tree <- first CEMiscError $ valToSyntaxTree treeVal
      macroExpand env =<< first CEMiscError (parseTree env tree)
    Just _ -> Left $ CECompilerBug "Attempting to macroexpand a non-macro"
    Nothing ->
      Left $ CECompilerBug "Attempting to macroexpand a nonexistent var"

getOnlyExpr :: [Stmt Me] -> Either CompileError (Typed Me (Expr Me))
getOnlyExpr stmts = case getExprs stmts of
  [] -> Left $ CEMiscError "Need an expr"
  [e] -> Right e
  es -> Left $ CEMiscError $ "Can only have one expr, got: " <> tshow es
 where
  getExprs = mapMaybe $ \case
   Expr e -> Just e
   Def _ _ -> Nothing
   DefMacro _ _ -> Nothing
   TypeDecl _ -> Nothing
   MacroStmt v _ _ -> absurd v

eval1 :: Env -> Expr Tc -> Either Text Val
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

  MacroExpr v _ _ -> absurd v

elimThunk :: Val -> Either Text Val
elimThunk (Thunk newenv e) = elimThunk =<< eval1 newenv e
elimThunk x = Right x

-- | If `val` matches `pat`, return Just a list of bound variables.
patternMatch :: Pattern Tc -> Val -> Maybe [(Name, Val)]
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
call (Thunk env expr) a = do
  func <- eval1 env expr
  call func a
call (Builtin (Builtin' _ b)) a = b a
call (Clos (Env syms) param body) a = do
  let syms2 = Map.insert param a syms
  eval1 (Env syms2) body
call val _ = error $ "attempted to call non-closure " ++ show val
