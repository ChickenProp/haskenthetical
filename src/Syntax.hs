module Syntax
  ( CompileError(..)
  , Pass(..), Ps, Tc, NoExt(..)
  , Name(..), HasName(..)
  , Env(..)
  , Stmt(..)
  , Expr(..)
  , Pattern(..)
  , Val(..)
  , Literal(..)
  , Builtin(..)
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
  , ppCompileError

  , DoBuiltin(..), getArg, mkBuiltin, mkBuiltinUnsafe
  ) where

import Prelude.Extra

import Data.Map.Strict (Map)
import qualified Data.Text as Text
import qualified Data.TreeDiff as TD
import GHC.Exts (IsString)

import Gist

data CompileError
  = CEParseError Text
  | CEMalformedExpr Text
  | CEMultiDeclareType Name
  | CEMultiDeclareConstructor Name
  | CEMultiDeclareValue Name
  | CEUnknownType Name
  | CEUnificationFail (MType Tc) (MType Tc)
  | CEKindMismatch (MType Tc) (MType Tc)
  | CETVarAsRoot (MType Tc)
  | CEUnboundVar Name
  | CEInfiniteType (TVar Tc) (MType Tc)
  | CEDeclarationTooGeneral (MType Tc) (MType Tc)
  | CECompilerBug Text
  deriving (Eq, Show)
instance Gist CompileError where
  gist = \case
    CEParseError x              -> TD.App "CEParseError" [gist x]
    CEMalformedExpr x           -> TD.App "CEMalformedExpr" [gist x]
    CEMultiDeclareType x        -> TD.App "CEMultiDeclareType" [gist x]
    CEMultiDeclareConstructor x -> TD.App "CEMultiDeclareConstructor" [gist x]
    CEMultiDeclareValue x       -> TD.App "CEMultiDeclareValue" [gist x]
    CEUnknownType x             -> TD.App "CEUnknownType" [gist x]
    CEUnificationFail x y       -> TD.App "CEUnificationFail" [gist x, gist y]
    CEKindMismatch x y          -> TD.App "CEKindMismatch" [gist x, gist y]
    CETVarAsRoot x              -> TD.App "CETVarAsRoot" [gist x]
    CEUnboundVar x              -> TD.App "CEUnboundVar" [gist x]
    CEInfiniteType x y          -> TD.App "CEInfiniteType" [gist x, gist y]
    CEDeclarationTooGeneral x y ->
      TD.App "CEDeclarationTooGeneral" [gist x, gist y]
    CECompilerBug x             -> TD.App "CECompilerBug" [gist x]

ppCompileError :: CompileError -> Text
ppCompileError = \case
  CEParseError t -> "Parse error:\n" <> t
  CEUnificationFail x y ->
    "Unification fail:\n  "
      <> tshow (prettyGist x)
      <> "\ndoes not unify with\n  "
      <> tshow (prettyGist y)
  CEInfiniteType x y ->
    "Infinite type: trying to unify\n  "
      <> tshow (prettyGist x)
      <> "\nwith\n  "
      <> tshow (prettyGist y)
  e -> tshow e

data Pass = Parsed | Typechecked
type Ps = 'Parsed
type Tc = 'Typechecked

data NoExt = NoExt deriving (Eq, Show, Ord)

newtype Name = Name Text
  deriving (Eq, Ord, Show, IsString, Semigroup, Monoid)
instance Gist Name where
  gist (Name n) = TD.App (Text.unpack n) []

class HasName a where
  getName :: a -> Name

-- Just so that `Val` can derive instances
data Builtin = Builtin' Name (Val -> Either Text Val)
instance Show Builtin where
  show (Builtin' (Name n) _) = "<" ++ Text.unpack n ++ ">"
instance Eq Builtin where
  Builtin' n1 _ == Builtin' n2 _ = n1 == n2

-- | A helper type to let us construct `Builtin` with do notation. Use with
-- `getArg` and `mkBuiltin`.
--
-- There's no Monad instance for this, and there can't be. Needs ApplicativeDo.
-- Some other datatype might let us achieve the same goal with more generality.
data DoBuiltin a = DoBuiltin [Name] ([Val] -> a)

instance Functor DoBuiltin where
  fmap f (DoBuiltin ns g) = DoBuiltin ns (f . g)

instance Applicative DoBuiltin where
  pure a = DoBuiltin [] (const a)
  (DoBuiltin ns1 f) <*> (DoBuiltin ns2 g) = DoBuiltin (ns1 ++ ns2) $ \vals ->
    let fVals = take (length ns1) vals
        gVals = drop (length ns1) vals
    in (f fVals) (g gVals)

getArg :: Name -> DoBuiltin Val
getArg n = DoBuiltin [n] head

mkBuiltin :: DoBuiltin (Either Text Val) -> Either Text Val
mkBuiltin (DoBuiltin [] f) = f []
mkBuiltin (DoBuiltin (n1:ns) f) = Right $ Builtin $ Builtin' n1 $ \v ->
  mkBuiltin $ DoBuiltin ns (\vs -> f (v : vs))

mkBuiltinUnsafe :: DoBuiltin (Either Text Val) -> Val
mkBuiltinUnsafe = either (error "Bad DoBuiltin") id . mkBuiltin

newtype Env = Env { unEnv :: Map Name Val }
  deriving (Eq, Show, Gist)

data TypeDecl = TypeDecl'
  { tdName :: Name
  , tdVars :: [Name]
  , tdConstructors :: [(Name, [MType Ps])]
  }
  deriving (Eq, Show)

instance Gist TypeDecl where
  gist (TypeDecl' {..}) =
    TD.App "TypeDecl" [gist tdName, gist tdVars, gist tdConstructors]

data Literal
  = Float Double
  | String Text
  deriving (Eq, Show)

instance Gist Literal where
  gist = \case
    Float n -> gist n
    String s -> gist s

data Val
  = Literal Literal
  | Builtin Builtin
  | Thunk Env Expr
  | Clos Env Name Expr
  | Tag Name [Val]
  deriving (Eq, Show)

instance Gist Val where
  gist = \case
    Literal l -> gist l
    Builtin (Builtin' n _) -> gist $ "<" <> n <> ">"
    Thunk env expr -> TD.App "Thunk" [gist env, gist expr]
    Clos _ _ _ -> gist ("Clos" :: Text)
    Tag (Name n) vals -> TD.App (Text.unpack n) (map gist vals)

data Pattern
  = PatConstr Name [Typed Pattern]
  | PatVal Name
  | PatLiteral Literal
  -- PatVal and PatLit aren't Typed because the parser couldn't distinguish
  --     Typed t $ PatVal $ UnTyped n
  --     UnTyped $ PatVal $ Typed t n
  deriving (Eq, Show)

instance Gist Pattern where
  gist = \case
    PatConstr n ps -> TD.App "PatConstr" [gist n, gist ps]
    PatVal n -> TD.App "PatVal" [gist n]
    PatLiteral l -> TD.App "PatLiteral" [gist l]

data Expr
  = Val Val
  | Var Name
  | Let [(Typed Name, Typed Expr)] (Typed Expr)
  | LetRec [(Typed Name, Typed Expr)] (Typed Expr)
  | Lam (Typed Name) (Typed Expr)
  | Call (Typed Expr) (Typed Expr)
  | IfMatch (Typed Expr) (Typed Pattern) (Typed Expr) (Typed Expr)
  deriving (Eq, Show)

instance Gist Expr where
  gist = \case
    Val v -> TD.App "Val" [gist v]
    Var n -> TD.App "Var" [gist n]
    Let bindings expr -> TD.App "Let" [gist bindings, gist expr]
    LetRec bindings expr -> TD.App "LetRec" [gist bindings, gist expr]
    Lam n expr -> TD.App "Lam" [gist n, gist expr]
    Call e1 e2 -> TD.App "Call" [gist e1, gist e2]
    IfMatch i pat e1 e2 -> TD.App "IfMatch" [gist i, gist pat, gist e1, gist e2]

data Stmt
  = Expr (Typed Expr)
  | Def (Typed Name) (Typed Expr)
  | TypeDecl TypeDecl
  deriving (Eq, Show)

instance Gist Stmt where
  gist = \case
    Expr e -> gist e
    Def n expr -> TD.App "Def" [gist n, gist expr]
    TypeDecl td -> gist td

data Kind = HType | Kind :*-> Kind
  deriving (Eq, Show, Ord)

infixr 4 :*->

class HasKind t where
  getKind :: HasCallStack => t -> Kind

data TVar (p :: Pass) = TV !(XTV p) Name
deriving instance Eq (TVar Ps)
deriving instance Eq (TVar Tc)
deriving instance Show (TVar Ps)
deriving instance Show (TVar Tc)
deriving instance Ord (TVar Ps)
deriving instance Ord (TVar Tc)

instance Gist (TVar p) where
  gist (TV _ n) = gist n

type family XTV (p :: Pass)
type instance XTV Ps = NoExt
type instance XTV Tc = Kind

instance HasName (TVar p) where getName (TV _ n) = n
instance HasKind (TVar Tc) where getKind (TV k _) = k

data TCon (p :: Pass) = TC !(XTC p) Name
deriving instance Eq (TCon Ps)
deriving instance Eq (TCon Tc)
deriving instance Show (TCon Ps)
deriving instance Show (TCon Tc)

instance Gist (TCon p) where
  gist (TC _ n) = gist n

type family XTC (p :: Pass)
type instance XTC Ps = NoExt
type instance XTC Tc = Kind

instance HasName (TCon p) where getName (TC _ n) = n
instance HasKind (TCon Tc) where getKind (TC k _) = k

data MType (p :: Pass)
  = TVar (TVar p)
  | TCon (TCon p)
  | TApp (MType p) (MType p)
deriving instance Eq (MType Ps)
deriving instance Eq (MType Tc)
deriving instance Show (MType Ps)
deriving instance Show (MType Tc)

instance Gist (MType p) where
  gist = \case
    TVar v -> gist v
    TCon c -> gist c
    TApp a b -> case gist a of
      TD.App n xs -> TD.App n (xs ++ [gist b])
      _ -> error "Unexpected gist"

instance HasKind (MType Tc) where
  getKind t = case t of
    TVar v -> getKind v
    TCon c -> getKind c
    t1 `TApp` t2 -> case (getKind t1, getKind t2) of
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

instance Gist (PType p) where
  gist (Forall vs mt) = TD.App "Forall" [gist vs, gist mt]

data Typed e = Typed (PType Ps) e | UnTyped e deriving (Eq, Show)

instance Gist e => Gist (Typed e) where
  gist (UnTyped e) = gist e
  gist (Typed t e) = TD.App ":" [gist t, gist e]

extractType :: Typed a -> (Maybe (PType Ps), a)
extractType = \case
  Typed t a -> (Just t, a)
  UnTyped a -> (Nothing, a)

mkTyped :: Maybe (PType Ps) -> a -> Typed a
mkTyped = maybe UnTyped Typed

rmType :: Typed a -> a
rmType = snd . extractType
