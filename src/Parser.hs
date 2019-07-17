module Parser (parseWholeFile, treesToExprs) where

import Prelude.Extra

import Data.Bifunctor (first)
import qualified Data.Char as Char
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

parseWholeFile :: String -> String -> Either Text [SyntaxTree]
parseWholeFile fName input =
  first (Text.pack . errorBundlePretty) $ parse stWholeFile fName input

treeToExpr :: SyntaxTree -> Either Text Expr
treeToExpr = \case
  STString s -> return $ Val (String s)
  STFloat f -> return $ Val (Float f)
  STBare b -> return $ Var (Name b)

  STTree [] -> Left "() is not currently a thing"
  STTree [STBare "λ", params, body] -> do
    b <- treeToExpr body
    let go xs = case xs of
          [] -> Left "lambda needs at least one arg"
          [(STBare x)] -> return $ Lam (Name x) b
          ((STBare x):xs') -> Lam (Name x) <$> go xs'
          _ -> Left "lambda args should be bare"
    case params of
      STTree xs -> go xs
      STBare x -> go [STBare x]
      _ -> Left "bad lambda arg"
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
  STTree (STBare "let":_) ->
    Left "bad let"

  STTree [STBare "def", STBare name, body] -> do
    b <- treeToExpr body
    return $ Def (Name name) b
  STTree (STBare "def" : _) ->
    Left "bad Def"

  STTree [a] -> treeToExpr a
  STTree [a1, a2] -> do
    a1' <- treeToExpr a1
    a2' <- treeToExpr a2
    return $ Call a1' a2'
  STTree (a1:a2:as) -> treeToExpr $ STTree $ STTree [a1, a2] : as

treesToExprs :: [SyntaxTree] -> Either Text [Expr]
treesToExprs = mapM treeToExpr
