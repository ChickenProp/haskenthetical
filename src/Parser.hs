module Parser (parseWholeFile, treesToExprs) where

import Prelude.Extra

import Data.Bifunctor (first)
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

stParser :: Parser SyntaxTree
stParser =
      STFloat <$> stFloat
  <|> STBare <$> stBare
  <|> STString <$> stString
  <|> STTree <$> stTree

stFloat :: Parser Double
stFloat = lexeme $ try (L.signed (pure ()) L.float)
               <|> try (fromIntegral @Int <$> L.signed (pure ()) L.decimal)

stString :: Parser Text
stString = Text.pack <$> between (symbol "\"") (symbol "\"") (many alphaNumChar)

stBare :: Parser Text
stBare = fmap Text.pack
  $ lexeme
  $ try
  $ some (alphaNumChar <|> char '+')

stTree :: Parser [SyntaxTree]
stTree = between (symbol "(") (symbol ")") (sepBy stParser sc)

stWholeFile :: Parser [SyntaxTree]
stWholeFile = between sc eof (sepBy stParser sc)

parseWholeFile :: String -> String -> Either Text [SyntaxTree]
parseWholeFile fName input =
  first (Text.pack . errorBundlePretty) $ parse stWholeFile fName input

treeToExpr :: SyntaxTree -> Either Text Expr
treeToExpr = \case
  STString s -> return $ Val (String s)
  STFloat f -> return $ Val (Float f)
  STBare b -> return $ Var (Name b)
  STTree [] -> Left "() is not currently a thing"
  STTree [STBare "lambda", params, body] -> do
    p <- case params of
      STBare x -> return $ Name x
      _ -> Left "lambda arg should be a single name"
    b <- treeToExpr body
    return $ Val $ Lam p b
  STTree (STBare "lambda":_) ->
    Left "bad lambda expr"
  STTree [STBare "let", STTree bindings, body] -> do
    bs <- parseBindings bindings
    b <- treeToExpr body
    return $ Let bs b
   where parseBindings [] = return []
         parseBindings (STTree [STBare n, v] : bs) = do
           v' <- treeToExpr v
           let b1 = (Name n, v')
           (b1 :) <$> parseBindings bs
         parseBindings x = Left $ "could not parse bindings:" <> tshow x
  STTree (a:as) -> do
    a' <- treeToExpr a
    as' <- mapM treeToExpr as
    return $ Call a' as'

treesToExprs :: [SyntaxTree] -> Either Text [Expr]
treesToExprs = mapM treeToExpr
