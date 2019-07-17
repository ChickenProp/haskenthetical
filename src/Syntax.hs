module Syntax
  ( Name(..)
  , Env(..)
  , Expr(..)
  , Val(..)
  , Builtin(..)
  ) where

import Prelude.Extra

import Data.Map.Strict (Map)
import qualified Data.Text as Text
import GHC.Exts (IsString)

newtype Name = Name { unName :: Text }
  deriving (Eq, Ord, Show, IsString)

-- Just so that `Val` can derive instances
data Builtin = Builtin' Name (Val -> Either Text Val)
instance Show Builtin where
  show (Builtin' (Name n) _) = "<" ++ Text.unpack n ++ ">"
instance Eq Builtin where
  Builtin' n1 _ == Builtin' n2 _ = n1 == n2

newtype Env = Env { unEnv :: Map Name Val }
  deriving (Eq, Show)

data Val
  = Float Double
  | String Text
  | Builtin Builtin
  | Clos Env Name Expr
  | Val :* Val
  | HLeft Val
  | HRight Val
  deriving (Eq, Show)

data Expr
  = Val Val
  | Var Name
  | Let [(Name, Expr)] Expr
  | Lam Name Expr
  | Call Expr Expr
  | Def Name Expr
  deriving (Eq, Show)
