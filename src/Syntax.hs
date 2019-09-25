module Syntax
  ( Name(..)
  , Env(..)
  , Expr(..)
  , Val(..)
  , Builtin(..)
  , Thunk(..)
  , Typed(..)
  , extractType
  , mkTyped
  , rmType
  ) where

import Prelude.Extra

import qualified Data.List.NonEmpty as NE
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

-- LetRec needs us to be able to evaluate an expr with a pointer to itself in
-- its environment. For that we need some form of delayed execution.
data Thunk = Thunk' Name (() -> Either Text Val)
instance Show Thunk where
  show (Thunk' (Name n) _) = "<thunk " ++ Text.unpack n ++ ">"
instance Eq Thunk where
  Thunk' n1 _ == Thunk' n2 _ = n1 == n2

newtype Env = Env { unEnv :: Map Name Val }
  deriving (Eq, Show)

data Val
  = Float Double
  | String Text
  | Builtin Builtin
  | Thunk Thunk
  | Clos Env Name Expr
  | Val :* Val
  | HLeft Val
  | HRight Val
  deriving (Eq, Show)

data Expr
  = Val Val
  | Var Name
  | Let [(Name, Expr)] Expr
  | LetRec [(Name, Expr)] Expr
  | Lam Name Expr
  | Call Expr Expr
  | Def Name Expr
  deriving (Eq, Show)

data Typed e = Typed (NE.NonEmpty Name) e | UnTyped e deriving (Eq, Show)

extractType :: Typed a -> (Maybe (NE.NonEmpty Name), a)
extractType = \case
  Typed t a -> (Just t, a)
  UnTyped a -> (Nothing, a)

mkTyped :: Maybe (NE.NonEmpty Name) -> a -> Typed a
mkTyped = maybe UnTyped Typed

rmType :: Typed a -> a
rmType = snd . extractType
