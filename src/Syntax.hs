module Syntax
  ( CompileError(..)
  , Pass(..), Ps, Me, Tc, NoExt(..)
  , Name(..), HasName(..)
  , SyntaxTree(..)
  , Env(..)
  , TopLevel(..)
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
  | CEMiscError Text
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
    CEMiscError x               -> TD.App "CEMiscError" [gist x]
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

data Pass = Parsed | MacroExpanded | Typechecked
type Ps = 'Parsed
type Me = 'MacroExpanded
type Tc = 'Typechecked

type family IfPassLE (p1 :: Pass) (p2 :: Pass)
type instance IfPassLE Ps Ps = NoExt
type instance IfPassLE Ps Me = NoExt
type instance IfPassLE Ps Tc = NoExt
type instance IfPassLE Me Ps = Void
type instance IfPassLE Me Me = NoExt
type instance IfPassLE Me Tc = NoExt
type instance IfPassLE Tc Ps = Void
type instance IfPassLE Tc Me = Void
type instance IfPassLE Tc Tc = NoExt

type family IfPassGT (p1 :: Pass) (p2 :: Pass)
type instance IfPassGT Ps Ps = Void
type instance IfPassGT Ps Me = Void
type instance IfPassGT Ps Tc = Void
type instance IfPassGT Me Ps = NoExt
type instance IfPassGT Me Me = Void
type instance IfPassGT Me Tc = Void
type instance IfPassGT Tc Ps = NoExt
type instance IfPassGT Tc Me = NoExt
type instance IfPassGT Tc Tc = Void

data NoExt = NoExt deriving (Eq, Show, Ord)

data SyntaxTree
  = STString Text
  | STFloat Double
  | STBare Text
  | STTree [SyntaxTree]
  deriving (Eq, Show)
instance Gist SyntaxTree where
  gist (STString t) = gist (tshow t)
  gist (STFloat f) = gist f
  gist (STBare t) = gist t
  gist (STTree ts) = TD.App "" (gist <$> ts)

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
  deriving (Show, Gist)

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
  | Thunk Env (Expr Tc)
  | Clos Env Name (Expr Tc)
  | Tag Name [Val]
  | Macro Val
  deriving (Show)

instance Gist Val where
  gist = \case
    Literal l -> gist l
    Builtin (Builtin' n _) -> gist $ "<" <> n <> ">"
    Thunk env expr -> TD.App "Thunk" [gist env, gist expr]
    Clos _ _ _ -> gist ("Clos" :: Text)
    Tag (Name n) vals -> TD.App (Text.unpack n) (map gist vals)
    Macro _ -> gist ("Macro" :: Text)

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

data Expr (p :: Pass)
  = Val Val
  | Var Name
  | Let [(Typed Name, Typed (Expr p))] (Typed (Expr p))
  | LetRec [(Typed Name, Typed (Expr p))] (Typed (Expr p))
  | Lam (Typed Name) (Typed (Expr p))
  | Call (Typed (Expr p)) (Typed (Expr p))
  | IfMatch (Typed (Expr p)) (Typed Pattern) (Typed (Expr p)) (Typed (Expr p))
  | MacroExpr !(XMacroThing p) Name [SyntaxTree]

deriving instance Show (Expr Ps)
deriving instance Show (Expr Me)
deriving instance Show (Expr Tc)

instance Gist (Expr p) where
  gist = \case
    Val v -> TD.App "Val" [gist v]
    Var n -> TD.App "Var" [gist n]
    Let bindings expr -> TD.App "Let" [gist bindings, gist expr]
    LetRec bindings expr -> TD.App "LetRec" [gist bindings, gist expr]
    Lam n expr -> TD.App "Lam" [gist n, gist expr]
    Call e1 e2 -> TD.App "Call" [gist e1, gist e2]
    IfMatch i pat e1 e2 -> TD.App "IfMatch" [gist i, gist pat, gist e1, gist e2]
    MacroExpr _ n trees -> TD.App "MacroExpr" [gist n, gist trees]

data Stmt (p :: Pass)
  = Expr (Typed (Expr p))
  | Def (Typed Name) (Typed (Expr p))
  | DefMacro Name (Typed (Expr p))
  | TypeDecl TypeDecl
  | MacroStmt !(XMacroThing p) Name [SyntaxTree]

deriving instance Show (Stmt Ps)
deriving instance Show (Stmt Me)
deriving instance Show (Stmt Tc)

type family XMacroThing (p :: Pass)
type instance XMacroThing Ps = NoExt
type instance XMacroThing Me = Void
type instance XMacroThing Tc = Void

instance Gist (Stmt p) where
  gist = \case
    Expr e -> gist e
    Def n expr -> TD.App "Def" [gist n, gist expr]
    DefMacro n expr -> TD.App "DefMacro" [gist n, gist expr]
    TypeDecl td -> gist td
    MacroStmt _ n trees -> TD.App "MacroStmt" [gist n, gist trees]

data TopLevel (p :: Pass)
  = DeclarationsPs !(IfPassLE p Ps) [SyntaxTree]
  | OtherTopLevelPs !(IfPassLE p Ps) SyntaxTree
  | Declarations !(IfPassGT p Ps) [Stmt p]
  | TopLevelDecl !(IfPassGT p Ps) (Stmt p)
  | TopLevelExpr !(IfPassGT p Ps) (Typed (Expr p))

deriving instance Show (TopLevel Ps)
deriving instance Show (TopLevel Me)
deriving instance Show (TopLevel Tc)

instance Gist (TopLevel p) where
  gist = \case
    DeclarationsPs _ x -> TD.App "Declarations" [gist x]
    OtherTopLevelPs _ x -> TD.App "OtherTopLevelPs" [gist x]
    Declarations _ x -> TD.App "Declarations" [gist x]
    TopLevelDecl _ x -> TD.App "TopLevelDecl" [gist x]
    TopLevelExpr _ x -> TD.App "TopLevelExpr" [gist x]

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
  tMacro :: MType a
  tSyntaxTree :: MType a
  tList :: MType a -> MType a

instance BuiltinTypes Ps where
  tFloat = TCon (TC NoExt "Float")
  tString = TCon (TC NoExt "String")
  tMacro = TCon (TC NoExt "Macro")
  tSyntaxTree = TCon (TC NoExt "SyntaxTree")
  tList t = TCon (TC NoExt "List") `TApp` t

instance BuiltinTypes Tc where
  tFloat = TCon (TC HType "Float")
  tString = TCon (TC HType "String")
  tMacro = TCon (TC HType "Macro")
  tSyntaxTree = TCon (TC HType "SyntaxTree")
  tList t = TCon (TC (HType :*-> HType) "List") `TApp` t

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
