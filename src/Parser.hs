module Parser (parseWholeFile, treesToExprs) where

import Prelude.Extra

import Data.Bifunctor (first)
import qualified Data.Char as Char
import Data.List (foldl1')
import qualified Data.Text as Text
import Data.Void (Void)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Syntax

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

data SyntaxTree
  = STString Text
  | STFloat Double
  | STBare Text
  | STTree [SyntaxTree]
  deriving (Eq, Show)

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
stString = Text.pack <$> between (symbol "\"") (symbol "\"") (many alphaNumChar)

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

treeToExpr :: SyntaxTree -> Either Text (Typed Expr)
treeToExpr = \case
  STString s -> unTyped $ Val (String s)
  STFloat f -> unTyped $ Val (Float f)
  STBare b -> unTyped $ Var (Name b)

  STTree [] -> Left "() is not currently a thing"

  STTree [STBare ":", typ, expr] -> do
    expr' <- treeToExpr expr
    case expr' of
      Typed _ _ -> Left "can't type something twice" -- any reason why not?
      UnTyped e -> flip Typed e <$> parsePType typ

  STTree [STBare "λ", params, body] -> do
    b <- treeToExpr body
    let go xs = case xs of
          [] -> Left "lambda needs at least one arg"
          [(STBare x)] -> return $ Lam (Name x) (rmType b)
          ((STBare x):xs') -> Lam (Name x) <$> go xs'
          _ -> Left "lambda args should be bare"
    case params of
      STTree xs -> UnTyped <$> go xs
      STBare x -> UnTyped <$> go [STBare x]
      _ -> Left "bad lambda arg"
  STTree (STBare "λ":_) ->
    Left "bad lambda expr"

  STTree [STBare "let", STTree bindings, body] -> do
    bs <- parseBindings bindings
    b <- treeToExpr body
    unTyped $ Let bs (rmType b)
   where parseBindings [] = return []
         parseBindings (STTree [STBare n, v] : bs) = do
           v' <- treeToExpr v
           let b1 = (Name n, rmType v')
           (b1 :) <$> parseBindings bs
         parseBindings x = Left $ "could not parse bindings:" <> tshow x
  STTree (STBare "let":_) ->
    Left "bad let"

  STTree [STBare "letrec", STTree bindings, body] -> do
    bs <- parseBindings bindings
    b <- treeToExpr body
    unTyped $ LetRec bs (rmType b)
   where parseBindings [] = return []
         parseBindings (STTree [STBare n, v] : bs) = do
           v' <- treeToExpr v
           let b1 = (Name n, rmType v')
           (b1 :) <$> parseBindings bs
         parseBindings x = Left $ "could not parse bindings:" <> tshow x
  STTree (STBare "letrec":_) ->
    Left "bad letrec"

  STTree [STBare "def", STBare name, body] -> do
    b <- treeToExpr body
    unTyped $ Def (Name name) (rmType b)
  STTree (STBare "def" : _) ->
    Left "bad Def"

  STTree (STBare "type" : STBare name : constructors) -> do
    constrs <- forM constructors $ \case
      STBare cname -> return (Name cname, [])
      STTree (STBare cname : args) -> fmap (Name cname,) $ mapM parseMType args
      _ -> Left "Bad constructor"
    unTyped $ TypeDecl $ TypeDecl' (Name name) [] constrs
  STTree (STBare "type" : _) ->
    Left "bad type"

  STTree [a] -> treeToExpr a
  STTree [a1, a2] -> do
    a1' <- treeToExpr a1
    a2' <- treeToExpr a2
    unTyped $ Call (rmType a1') (rmType a2')
  STTree (a1:a2:as) -> treeToExpr $ STTree $ STTree [a1, a2] : as
 where
  unTyped = return . UnTyped

treesToExprs :: [SyntaxTree] -> Either CompileError [Typed Expr]
treesToExprs = mapM (first CEMalformedExpr . treeToExpr)

parsePType :: SyntaxTree -> Either Text (PType Ps)
parsePType tree = Forall [] <$> parseMType tree

parseMType :: SyntaxTree -> Either Text (MType Ps)
parseMType = \case
  STBare n -> return $ TCon $ TC NoExt $ Name n
  STFloat _ -> Left "Cannot put a Float in a type"
  STString _ -> Left "Cannot put a String in a type"
  STTree [] -> Left "Empty type"
  STTree xs -> do
    ts <- mapM parseMType xs
    return $ foldl1' TApp ts
