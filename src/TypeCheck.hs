module TypeCheck (runTypeCheck, defaultTypes) where

import Prelude.Extra

import Control.Monad (replicateM)
import Control.Monad.Trans (lift)
import Control.Monad.RWS.Strict (RWST, runRWST, tell, local, get, put, ask)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text

import Syntax

newtype TVar = TV Text deriving (Eq, Show, Ord)
newtype TCon = TC Text deriving (Eq, Show)

data MType = TVar TVar | TCon TCon | MType :-> MType | MType ::* MType
  deriving (Eq, Show)

infixr 4 :-> -- 4 chosen fairly arbitrarily
infixr 4 ::*

tFloat, tString :: MType
tFloat = TCon (TC "Float")
tString = TCon (TC "String")

data PType = Forall [TVar] MType
  deriving (Eq, Show)

newtype TypeEnv = TypeEnv { _unTypeEnv :: Map Name PType }
type Constraint = (MType, MType)

tInsert :: Name -> PType -> TypeEnv -> TypeEnv
tInsert n t (TypeEnv m) = TypeEnv $ Map.insert n t m

tLookup :: Name -> TypeEnv -> Maybe PType
tLookup n (TypeEnv m) = Map.lookup n m

extending :: Name -> PType -> Infer a -> Infer a
extending n t m = local (tInsert n t) m

-- TODO: unify this with defaultSymbols
defaultTypes :: TypeEnv
defaultTypes = TypeEnv $ Map.fromList
  [ ("+", Forall [] (tFloat :-> tFloat :-> tFloat))
  , ("three", Forall [] tFloat)
  , (",", Forall [TV "a", TV "b"]
      $ TVar (TV "a") :-> TVar (TV "b") :-> (TVar (TV "a") ::* TVar (TV "b")))
  , ("car", Forall [TV "a", TV "b"]
      $ (TVar (TV "a") ::* TVar (TV "b")) :-> TVar (TV "a"))
  , ("cdr", Forall [TV "a", TV "b"]
      $ (TVar (TV "a") ::* TVar (TV "b")) :-> TVar (TV "b"))
  ]

newtype Subst = Subst { _subst :: Map TVar MType }
  deriving (Eq, Show)

nullSubst :: Subst
nullSubst = Subst Map.empty

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set TVar

instance Substitutable MType where
  apply _ (TCon a) = TCon a
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  apply s (t1 :-> t2)  = apply s t1 :-> apply s t2
  apply s (t1 ::* t2)  = apply s t1 ::* apply s t2

  ftv (TCon _) = Set.empty
  ftv (TVar a) = Set.singleton a
  ftv (t1 :-> t2) = ftv t1 `Set.union` ftv t2
  ftv (t1 ::* t2) = ftv t1 `Set.union` ftv t2

instance Substitutable PType where
  apply (Subst s) (Forall as t) =
    Forall as $ apply (Subst $ foldr Map.delete s as) t
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable a => Substitutable [a] where
  apply s as = fmap (apply s) as
  ftv as = Set.unions (fmap ftv as)

instance Substitutable Constraint where
  apply s (t1, t2) = (apply s t1, apply s t2)
  ftv (t1, t2) = ftv t1 `Set.union` ftv t2

instance Substitutable TypeEnv where
  apply s (TypeEnv m) = TypeEnv $ apply s <$> m
  ftv (TypeEnv m) = ftv $ Map.elems m


-- Typechecking has two main phases. In the Infer phase, we generate a type for
-- the expression, along with a list of constraints of the form "this type and
-- this type must be equal". In the Solve phase, we generate a substitution from
-- those constraints, which expands all type variables as far as possible to
-- concrete types.

runTypeCheck :: TypeEnv -> Expr -> Either Text PType
runTypeCheck env expr = do
  (ty, _, constraints) <- runRWST (infer expr) env (InferState letters)
  subst <- solver1 constraints
  return $ generalize env $ apply subst ty
  where letters = map (TV . Text.pack) $ [1..] >>= flip replicateM ['a'..'z']

---

data InferState = InferState { _vars :: [TVar] }
type Infer a = RWST TypeEnv [Constraint] InferState (Either Text) a

genSym :: Infer MType
genSym = do
  InferState vars <- get
  put $ InferState (tail vars)
  return $ TVar (head vars)

instantiate :: PType -> Infer MType
instantiate (Forall as t) = do
  as' <- mapM (const genSym) as
  let subst = Subst $ Map.fromList (zip as as')
  return $ apply subst t

generalize :: TypeEnv -> MType -> PType
generalize env t = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env

lookupEnv :: Name -> Infer MType
lookupEnv n = do
  env <- ask
  case tLookup n env of
    Nothing -> lift $ Left $ "unbound variable " <> tshow n
    Just t -> instantiate t

unify :: MType -> MType -> Infer ()
unify t1 t2 = tell [(t1, t2)]

infer :: Expr -> Infer MType
infer expr = case expr of
  Val (Float _) -> return tFloat
  Val (String _) -> return tString

  Var n -> lookupEnv n

  Lam x e -> do
    tv <- genSym
    t <- extending x (Forall [] tv) (infer e)
    return $ tv :-> t

  Let [] e -> infer e
  Let ((n, e1):bs) e -> do
    env <- ask
    t1 <- infer e1
    let sc = generalize env t1
    t2 <- extending n sc (infer $ Let bs e)
    return t2

  Call fun a -> do
    t1 <- infer fun
    t2 <- infer a
    tv <- genSym
    unify t1 (t2 :-> tv)
    return tv

  _ -> error "unimplemented"

---

type Unifier = (Subst, [Constraint])
type Solve a = Either Text a

-- | Subst that applies s2 followed by s1
compose :: Subst -> Subst -> Subst
s1@(Subst s1') `compose` (Subst s2') =
  Subst $ fmap (apply s1) s2' `Map.union` s1'

-- | Subst that binds variable a to type t
bind :: TVar -> MType -> Solve Subst
bind a t | t == TVar a = return nullSubst
         | a `Set.member` ftv t = Left "infinite type"
         | otherwise = return $ Subst $ Map.singleton a t

unifies :: MType -> MType -> Solve Subst
unifies t1 t2 | t1 == t2 = return nullSubst
unifies (TVar v) t = bind v t
unifies t (TVar v) = bind v t
unifies (t11 :-> t12) (t21 :-> t22) = unifiesMany [t11, t12] [t21, t22]
unifies (t11 ::* t12) (t21 ::* t22) = unifiesMany [t11, t12] [t21, t22]
unifies a b = Left $ "unification fail: " <> tshow a <> " is not " <> tshow b

unifiesMany :: [MType] -> [MType] -> Solve Subst
unifiesMany [] [] = return nullSubst
unifiesMany (t1: ts1) (t2 : ts2) = do
  su1 <- unifies t1 t2
  su2 <- unifiesMany (apply su1 ts1) (apply su1 ts2)
  return (su2 `compose` su1)
unifiesMany _ _ = Left "unification mismatch"

solver :: Unifier -> Solve Subst
solver (su, cs) =
 case cs of
   [] -> return su
   ((t1, t2) : cs0) -> do
     su1 <- unifies t1 t2
     solver (su1 `compose` su, apply su1 cs0)

solver1 :: [Constraint] -> Solve Subst
solver1 cs = solver (nullSubst, cs)
