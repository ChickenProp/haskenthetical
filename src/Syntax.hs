module Syntax
  ( Pass(..), Ps, Tc
  , Name(..)
  , Env(..)
  , Expr(..)
  , Val(..)
  , Builtin(..)
  , Thunk(..)
  , Typed(..)
  , MType(..)
  , PType(..)
  , TCon(..)
  , TVar(..)
  , BuiltinTypes(..)
  , (+->)
  , (+:*)
  , (+:+)
  , extractType
  , mkTyped
  , rmType
  ) where

import Prelude.Extra

import Data.Map.Strict (Map)
import qualified Data.Text as Text
import Data.Void (Void)
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

data Kind = HType | Kind :*-> Kind
  deriving (Eq, Show)

newtype TVar = TV Text deriving (Eq, Show, Ord)

data Pass = Parsed | Typechecked
type Ps = 'Parsed
type Tc = 'Typechecked

data TCon (p :: Pass) = TC (XTC p) Text
deriving instance Eq (TCon Ps)
deriving instance Eq (TCon Tc)
deriving instance Show (TCon Ps)
deriving instance Show (TCon Tc)

type family XTC (p :: Pass)
type instance XTC Ps = Void
type instance XTC Tc = Kind

data MType (p :: Pass)
  = TVar TVar
  | TCon (TCon p)
  | TApp (MType p) (MType p)
deriving instance Eq (MType Ps)
deriving instance Eq (MType Tc)
deriving instance Show (MType Ps)
deriving instance Show (MType Tc)

(+->) :: MType Tc -> MType Tc -> MType Tc
a +-> b = TCon (TC (HType :*-> HType) "->") `TApp` a `TApp` b

(+:*) :: MType Tc -> MType Tc -> MType Tc
a +:* b = TCon (TC (HType :*-> HType) ",") `TApp` a `TApp` b

(+:+) :: MType Tc -> MType Tc -> MType Tc
a +:+ b = TCon (TC (HType :*-> HType) "+") `TApp` a `TApp` b

infixr 4 +-> -- 4 chosen fairly arbitrarily
infixr 4 +:*
infixr 4 +:+

class BuiltinTypes a where
  tFloat :: MType a
  tString :: MType a

instance BuiltinTypes Ps where
  tFloat = TCon (TC undefined "Float")
  tString = TCon (TC undefined "String")

instance BuiltinTypes Tc where
  tFloat = TCon (TC HType "Float")
  tString = TCon (TC HType "String")

data PType (p :: Pass) = Forall [TVar] (MType p)
deriving instance Eq (PType Ps)
deriving instance Eq (PType Tc)
deriving instance Show (PType Ps)
deriving instance Show (PType Tc)

data Typed e = Typed (PType Ps) e | UnTyped e deriving (Eq, Show)

extractType :: Typed a -> (Maybe (PType Ps), a)
extractType = \case
  Typed t a -> (Just t, a)
  UnTyped a -> (Nothing, a)

mkTyped :: Maybe (PType Ps) -> a -> Typed a
mkTyped = maybe UnTyped Typed

rmType :: Typed a -> a
rmType = snd . extractType
