module Parser
  ( parseMType
  , parsePType
  , parseWholeFile
  , treeToExpr
  , treeToStmt
  , treesToStmts
  , treeToTopLevel
  ) where

import Prelude.Extra

import Data.Bifunctor (first)
import qualified Data.Char as Char
import Data.List (foldl1')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Void (Void)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Env
import Syntax

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineComment empty
 where
  lineComment = try $ do
    (string "#!" <|> string "#")
    lookAhead space1
    void $ takeWhileP (Just "character") (/= '\n')

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

-- Having to list all special characters in one place seems awkward.
isNonSyntax :: Char -> Bool
isNonSyntax c = Char.isPrint c
             && not (Char.isSpace c)
             && notElem c ("()\"" :: String)

stParser :: Parser SyntaxTree
stParser =
  -- A bareword can contain numeric characters, it just can't start with
  -- something that might parse as a number. We can't simply forbid them to
  -- start with numeric characters, because we need to forbid e.g. "+5x" while
  -- accepting "+x".
      STBare <$> (notFollowedBy stFloat' >> stBare)
  <|> STFloat <$> stFloat
  <|> STString <$> stString
  <|> STTree <$> stTree

stFloat' :: Parser Double
stFloat' = try (L.signed (pure ()) L.float)
       <|> try (fromIntegral @Int <$> L.signed (pure ()) L.decimal)

stFloat :: Parser Double
stFloat =
  -- This forbids `5x` from being parsed as `5 x`. But it accepts `5"foo"` as `5
  -- "foo"`. We could add more `notFollowedBy`, but maybe the `sepBy` in
  -- `stTree` is actually the place to look? But that's awkward because we do
  -- want `(foo)(bar)` to work. So probably we just need to replace `sepBy` with
  -- something custom. But this works for now.
  lexeme $ stFloat' <* notFollowedBy stBare

stString :: Parser Text
stString = Text.pack <$> (char '"' >> manyTill charLiteral (char '"'))

charLiteral :: Parser Char
charLiteral = label "literal char" $ anySingle >>= \case
  '\\' -> anySingle >>= \case
    '\\' -> pure '\\'
    '"' -> pure '"'
    'n' -> pure '\n'
    x -> failure (Just $ Tokens $ x :| [])
                 (Set.fromList $ Tokens . (:| []) <$> "\"\\n")
  x -> pure x

stBare :: Parser Text
stBare = fmap Text.pack
  $ lexeme
  $ takeWhile1P (Just "non-syntax character") isNonSyntax

stTree :: Parser [SyntaxTree]
stTree = between (symbol "(") (symbol ")") (sepBy stParser sc)

stWholeFile :: Parser [SyntaxTree]
stWholeFile = between sc eof (sepBy stParser sc)

parseWholeFile :: String -> String -> Either CompileError [SyntaxTree]
parseWholeFile fName input =
  first (CEParseError . Text.pack . errorBundlePretty)
    $ parse stWholeFile fName input

treeToTopLevel :: SyntaxTree -> TopLevel Ps
treeToTopLevel = \case
  STTree (STBare "declarations" : body) -> DeclarationsPs NoExt body
  t -> OtherTopLevelPs NoExt t

treeToStmt :: FullEnv -> SyntaxTree -> Either Text (Stmt Ps)
treeToStmt env = \case
  STTree [STBare "def", name, body] -> do
    n <- parseTyped parseName env name
    b <- parseTyped (treeToExpr env) env body
    return $ Def n b
  STTree (STBare "def" : _) ->
    Left "bad def"

  STTree [STBare "defmacro", name, body] -> do
    n <- parseName name
    b <- parseTyped (treeToExpr env) env body
    return $ DefMacro n b
  STTree (STBare "defmacro" : _) ->
    Left "bad defmacro"

  STTree (STBare "type" : typeCon : dataCons) -> do
    let parseTCon :: MType Ps -> Either Text (Name, [Name])
        parseTCon = \case
          TCon (TC NoExt n) -> return (n, [])
          TVar _ -> Left "can't declare a type variable"
          _ `TApp` (TCon _) -> Left "type constructor where I expected a var"
          _ `TApp` (TApp _ _) -> Left "type application where I expected a var"
          a `TApp` (TVar (TV NoExt v)) -> fmap (++ [v]) <$> parseTCon a
          _ `TApp` (MacroMType NoExt _ _) -> Left "macro where I expected a var"
          MacroMType NoExt _ _ -> Left "can't use macros in type declarations"
    (typeName, typeVars) <- parseTCon =<< parseMType env typeCon

    constrs <- forM dataCons $ \case
      STBare cname -> return (Name cname, [])
      STTree (STBare cname : args) ->
        fmap (Name cname,) $ mapM (parseMType env) args
      _ -> Left "Bad constructor"
    return $ TypeDecl $ TypeDecl' typeName typeVars constrs
  STTree (STBare "type" : _) ->
    Left "bad type"

  STTree (STBare n : rest) | isMacro env n ->
    return $ MacroStmt NoExt (Name n) rest

  x -> Expr <$> parseTyped (treeToExpr env) env x

parseTyped
  :: (SyntaxTree -> Either Text a)
  -> FullEnv
  -> SyntaxTree
  -> Either Text (Typed Ps a)
parseTyped parseUntyped env = \case
  STTree [STBare ":", x, typ] -> do
    parsed <- parseTyped parseUntyped env x
    case parsed of
      -- maybe ideally `Typed` would be isomorphic to `([Type], )`
      Typed _ _ -> Left "Can't type something twice"
      UnTyped e -> Typed <$> parsePType env typ <*> pure e
  STTree (STBare ":" : _) -> do
      Left "Bad type annotation"
  x -> UnTyped <$> parseUntyped x

parseName :: SyntaxTree -> Either Text Name
parseName = \case
  STBare n -> return $ Name n
  x -> Left $ "could not parse name: " <> tshow x

treeToExpr :: FullEnv -> SyntaxTree -> Either Text (Expr Ps)
treeToExpr env = \case
  STString s -> return $ Val (Literal $ String s)
  STFloat f -> return $ Val (Literal $ Float f)
  STBare b -> return $ Var (Name b)

  STTree [] -> Left "() is not currently a thing"

  STTree [STBare "λ", params, body] -> do
    b <- parseTyped (treeToExpr env) env body
    let go xs = case xs of
          [] -> Left "lambda needs at least one arg"
          [n] -> Lam <$> parseTyped parseName env n <*> pure b
          (n:ns) -> Lam <$> parseTyped parseName env n <*> (UnTyped <$> go ns)
    case params of
      STTree xs -> go xs
      STBare x -> go [STBare x]
      _ -> Left "bad lambda arg"
  STTree (STBare "λ":_) ->
    Left "bad lambda expr"

  STTree [STBare "let", STTree bindings, body] -> do
    bs <- parseBindings bindings
    b <- parseTyped (treeToExpr env) env body
    return $ Let bs b
  STTree (STBare "let" : _) ->
    Left "bad let"

  STTree [STBare "letrec", STTree bindings, body] -> do
    bs <- parseBindings bindings
    b <- parseTyped (treeToExpr env) env body
    return $ LetRec bs b
  STTree (STBare "letrec":_) ->
    Left "bad letrec"

  STTree [STBare "if~", inTree, pattern, thenTree, elseTree] -> do
    i <- parseTyped (treeToExpr env) env inTree
    p <- parseTyped (parsePattern env) env pattern
    t <- parseTyped (treeToExpr env) env thenTree
    e <- parseTyped (treeToExpr env) env elseTree
    return $ IfMatch i p t e
  STTree (STBare "if~" : _) ->
    Left "bad if~"

  STTree (STBare n : rest) | isMacro env n ->
    return $ MacroExpr NoExt (Name n) rest

  STTree [a] -> (treeToExpr env) a
  STTree [a1, a2] -> do
    a1' <- parseTyped (treeToExpr env) env a1
    a2' <- parseTyped (treeToExpr env) env a2
    return $ Call a1' a2'
  STTree (a1:a2:as) -> (treeToExpr env) $ STTree $ STTree [a1, a2] : as
 where
  parseBindings [] = return []
  parseBindings (STTree [name, v] : bs) = do
    n <- parseTyped parseName env name
    v' <- parseTyped (treeToExpr env) env v
    ((n, v') :) <$> parseBindings bs
  parseBindings x = Left $ "could not parse bindings: " <> tshow x

treesToStmts :: FullEnv -> [SyntaxTree] -> Either CompileError [Stmt Ps]
treesToStmts env = mapM (first CEMalformedExpr . treeToStmt env)

parsePattern :: FullEnv -> SyntaxTree -> Either Text (Pattern Ps)
parsePattern env = \case
  STBare n -> return $ case Text.stripPrefix "$" n of
    Just n' -> PatVal $ Name n'
    Nothing -> PatConstr (Name n) []
  STFloat n -> return $ PatLiteral $ Float n
  STString s -> return $ PatLiteral $ String s
  STTree [] -> Left "Empty pattern"
  STTree (x:xs) -> parsePattern env x >>= \case
    PatLiteral _ -> Left "Cannot have a literal at the head of a pattern"
    PatVal _ -> Left "Cannot have a var at the head of a pattern"
    PatConstr n ys -> do
      xs' <- traverse (parseTyped (parsePattern env) env) xs
      return $ PatConstr n (ys ++ xs')

parsePType :: FullEnv -> SyntaxTree -> Either Text (PType Ps)
parsePType env = \case
  -- There's no way to parse a `Forall [] (MacroMType ...)`. But if the macro
  -- expands into an MType, then as a PType it'll expand into a `Forall [] ...`,
  -- so we don't lose expressivity.
  STTree (STBare n : rest) | isMacro env n ->
    return $ MacroPType NoExt (Name n) rest
  tree -> Forall [] <$> parseMType env tree

parseMType :: FullEnv -> SyntaxTree -> Either Text (MType Ps)
parseMType env = \case
  STBare n -> return $ case Text.take 1 n of
    "$" -> TVar $ TV NoExt $ Name n
    _ -> TCon $ TC NoExt $ Name n
  STFloat _ -> Left "Cannot put a Float in a type"
  STString _ -> Left "Cannot put a String in a type"
  STTree [] -> Left "Empty type"
  STTree (STBare n : rest) | isMacro env n ->
    return $ MacroMType NoExt (Name n) rest
  STTree xs -> do
    ts <- mapM (parseMType env) xs
    return $ foldl1' TApp ts

isMacro :: FullEnv -> Text -> Bool
isMacro env n = case Map.lookup (Name n) (feVars env) of
  Nothing -> False
  Just (t, _) -> t == Forall [] tMacro
