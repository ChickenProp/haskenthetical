module Syntax (Name(..), Expr(..), Val(..), Builtin(..)) where

import qualified Data.Text as Text
import Data.Text (Text)
import GHC.Exts (IsString)

newtype Name = Name { unName :: Text }
  deriving (Eq, Ord, Show, IsString)

-- Just so that `Val` can derive instances
data Builtin = Builtin' Name (Val -> Either Text Val)
instance Show Builtin where
  show (Builtin' (Name n) _) = "<" ++ Text.unpack n ++ ">"
instance Eq Builtin where
  Builtin' n1 _ == Builtin' n2 _ = n1 == n2

data Val
  = Float Double
  | String Text
  | Builtin Builtin
  | Lam Name Expr
  deriving (Eq, Show)

data Expr
  = Val Val
  | Var Name
  | Call Expr [Expr]
  | Def Name [Name] Expr
  deriving (Eq, Show)
