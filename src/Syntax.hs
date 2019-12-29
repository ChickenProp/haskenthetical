module Syntax
  ( Pass(..), Ps, Tc, NoExt(..)
  , Name(..)
  , Env(..)
  , Expr(..)
  , Val(..)
  , Builtin(..)
  , Thunk(..)
  , Typed(..)
  , TypeDecl(..)
  , MType(..)
  , PType(..)
  , TCon(..)
  , TVar(..)
  , Kind(..), HasKind(..)
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
import GHC.Exts (IsString)

data Pass = Parsed | Typechecked
type Ps = 'Parsed
type Tc = 'Typechecked

data NoExt = NoExt deriving (Eq, Show, Ord)

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

data TypeDecl = TypeDecl'
  { tdName :: Name
  , tdVars :: [Name]
  , tdConstructors :: [(Name, [Name])]
  }
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
  | Tag Name [Val]
  deriving (Eq, Show)

data Expr
  = Val Val
  | Var Name
  | Let [(Name, Expr)] Expr
  | LetRec [(Name, Expr)] Expr
  | Lam Name Expr
  | Call Expr Expr
  | Def Name Expr
  | TypeDecl TypeDecl
  deriving (Eq, Show)

data Kind = HType | Kind :*-> Kind
  deriving (Eq, Show, Ord)

infixr 4 :*->

class HasKind t where
  kind :: t -> Kind

data TVar (p :: Pass) = TV !(XTV p) Text
deriving instance Eq (TVar Ps)
deriving instance Eq (TVar Tc)
deriving instance Show (TVar Ps)
deriving instance Show (TVar Tc)
deriving instance Ord (TVar Ps)
deriving instance Ord (TVar Tc)

type family XTV (p :: Pass)
type instance XTV Ps = NoExt
type instance XTV Tc = Kind

instance HasKind (TVar Tc) where kind (TV k _) = k

data TCon (p :: Pass) = TC !(XTC p) Name
deriving instance Eq (TCon Ps)
deriving instance Eq (TCon Tc)
deriving instance Show (TCon Ps)
deriving instance Show (TCon Tc)

type family XTC (p :: Pass)
type instance XTC Ps = NoExt
type instance XTC Tc = Kind

instance HasKind (TCon Tc) where kind (TC k _) = k

data MType (p :: Pass)
  = TVar (TVar p)
  | TCon (TCon p)
  | TApp (MType p) (MType p)
deriving instance Eq (MType Ps)
deriving instance Eq (MType Tc)
deriving instance Show (MType Ps)
deriving instance Show (MType Tc)

instance HasKind (MType Tc) where
  kind t = case t of
    TVar v -> kind v
    TCon c -> kind c
    t1 `TApp` t2 -> case (kind t1, kind t2) of
      (k11 :*-> k12, k2) | k11 == k2 -> k12
      _ -> error $ "Type with malformed kind: " ++ show t

(+->) :: MType Tc -> MType Tc -> MType Tc
a +-> b = TCon (TC (HType :*-> HType :*-> HType) "->") `TApp` a `TApp` b

(+:*) :: MType Tc -> MType Tc -> MType Tc
a +:* b = TCon (TC (HType :*-> HType :*-> HType) ",") `TApp` a `TApp` b

(+:+) :: MType Tc -> MType Tc -> MType Tc
a +:+ b = TCon (TC (HType :*-> HType :*-> HType) "+") `TApp` a `TApp` b

infixr 4 +-> -- 4 chosen fairly arbitrarily
infixr 4 +:*
infixr 4 +:+

class BuiltinTypes a where
  tFloat :: MType a
  tString :: MType a

instance BuiltinTypes Ps where
  tFloat = TCon (TC NoExt "Float")
  tString = TCon (TC NoExt "String")

instance BuiltinTypes Tc where
  tFloat = TCon (TC HType "Float")
  tString = TCon (TC HType "String")

data PType (p :: Pass) = Forall [TVar p] (MType p)
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
