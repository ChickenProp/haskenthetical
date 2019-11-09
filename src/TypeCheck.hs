module TypeCheck
  ( TypeEnv(..)
  , runTypeCheck
  ) where

import Prelude.Extra

import Control.Monad (replicateM)
import Control.Monad.Except (liftEither)
import Control.Monad.Trans (lift)
import Control.Monad.RWS.Strict
  (RWST, runRWST, tell, local, get, put, ask, listen)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text

import Syntax

newtype TypeEnv = TypeEnv { _unTypeEnv :: Map Name (PType Tc) } deriving (Show)
type Constraint = (MType Tc, MType Tc)

tInsert :: Name -> PType Tc -> TypeEnv -> TypeEnv
tInsert n t (TypeEnv m) = TypeEnv $ Map.insert n t m

tInsertMany :: [(Name, PType Tc)] -> TypeEnv -> TypeEnv
tInsertMany bs (TypeEnv m) = TypeEnv $ Map.union (Map.fromList bs) m

tLookup :: Name -> TypeEnv -> Maybe (PType Tc)
tLookup n (TypeEnv m) = Map.lookup n m

extending :: Name -> PType Tc -> Infer a -> Infer a
extending n t m = local (tInsert n t) m

newtype Subst = Subst { _subst :: Map TVar (MType Tc) }
  deriving (Eq, Show)

nullSubst :: Subst
nullSubst = Subst Map.empty

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set TVar

instance Substitutable (MType Tc) where
  apply _ (TCon a) = TCon a
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  apply s (t1 `TApp` t2) = apply s t1 `TApp` apply s t2

  ftv (TCon _) = Set.empty
  ftv (TVar a) = Set.singleton a
  ftv (t1 `TApp` t2) = ftv t1 `Set.union` ftv t2

instance Substitutable (PType Tc) where
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
--
-- But they can't be totally separated, because we need to run the solver
-- whenever we generalize a variable during inference. Otherwise, suppose we
-- have a type variable `e` and we know it unifies with `Float`. We'll
-- generalize `e` to `Forall [e] e`, and then that won't unify with `Float`. By
-- running the solver, we instead generalize `Float` to `Forall [] Float`.

runTypeCheck :: TypeEnv -> Typed Expr -> Either Text (PType Tc)
runTypeCheck env expr = do
  (ty, _, constraints) <- runRWST (inferTyped expr) env (InferState letters)
  subst <- solver1 constraints
  return $ generalize env $ apply subst ty
  where letters = map (TV . Text.pack) $ [1..] >>= flip replicateM ['a'..'z']

---

data InferState = InferState { _vars :: [TVar] }
type Infer a = RWST TypeEnv [Constraint] InferState (Either Text) a

genSym :: Infer (MType Tc)
genSym = do
  InferState vars <- get
  put $ InferState (tail vars)
  return $ TVar (head vars)

instantiate :: PType Tc -> Infer (MType Tc)
instantiate (Forall as t) = do
  as' <- mapM (const genSym) as
  let subst = Subst $ Map.fromList (zip as as')
  return $ apply subst t

generalize :: TypeEnv -> MType Tc -> PType Tc
generalize env t = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env

lookupEnv :: Name -> Infer (MType Tc)
lookupEnv n = do
  env <- ask
  case tLookup n env of
    Nothing -> lift $ Left $ "unbound variable " <> tshow n
    Just t -> instantiate t

unify :: MType Tc -> MType Tc -> Infer ()
unify t1 t2 = tell [(t1, t2)]

ps2tc_PType :: PType Ps -> Infer (PType Tc)
ps2tc_PType = \case
  Forall [] (TCon (TC _ n)) -> case n of
    "Float" -> return $ Forall [] tFloat
    "String" -> return $ Forall [] tString
    _ -> error $ "Unexpected type " ++ show n
  _ -> error "Unhandled case in ps2tc_Ptype"

inferTyped :: Typed Expr -> Infer (MType Tc)
inferTyped (UnTyped e) = infer e
inferTyped (Typed t e) = do
  t' <- instantiate =<< ps2tc_PType t
  e' <- infer e
  unify t' e'
  return t'

infer :: Expr -> Infer (MType Tc)
infer expr = case expr of
  Val (Float _) -> return tFloat
  Val (String _) -> return tString
  Val v -> error $ "unexpected Val during typechecking: " ++ show v

  Var n -> lookupEnv n

  Lam x e -> do
    tv <- genSym
    t <- extending x (Forall [] tv) (infer e)
    return $ tv +-> t

  Let [] e -> infer e
  Let ((n, e1):bs) e -> do
    env <- ask
    (t1, constraints) <- listen $ infer e1
    subst <- liftEither $ solver1 constraints
    let gen = generalize env (apply subst t1)
    t2 <- extending n gen (infer $ Let bs e)
    return t2

  LetRec bindings e -> do
    env <- ask
    tvs <- forM bindings $ \_ -> genSym
    let tBindings = flip map (zip tvs bindings) $ \(tv, (n, _)) ->
          (n, Forall [] tv)
    (t1s, constraints) <- listen $ forM (zip tvs bindings)
      $ \(tv, (_, e1)) -> do
        t1 <- local (tInsertMany tBindings) (infer e1)
        unify tv t1
        return t1
    subst <- liftEither $ solver1 constraints
    let gens = flip map (zip bindings t1s) $ \((n, _), t1) ->
          (n, generalize env (apply subst t1))
    seq gens $ local (tInsertMany gens) $ infer e

  Call fun a -> do
    t1 <- infer fun
    t2 <- infer a
    tv <- genSym
    unify t1 (t2 +-> tv)
    return tv

  Def _ _ -> error "shouldn't have a Def here"

---

type Unifier = (Subst, [Constraint])
type Solve a = Either Text a

-- | Subst that applies s2 followed by s1
compose :: Subst -> Subst -> Subst
s1@(Subst s1') `compose` (Subst s2') =
  Subst $ fmap (apply s1) s2' `Map.union` s1'

-- | Subst that binds variable a to type t
bind :: TVar -> MType Tc -> Solve Subst
bind a t | t == TVar a = return nullSubst
         | a `Set.member` ftv t = Left "infinite type"
         | otherwise = return $ Subst $ Map.singleton a t

unifies :: MType Tc -> MType Tc -> Solve Subst
unifies t1 t2 | t1 == t2 = return nullSubst
unifies (TVar v) t = bind v t
unifies t (TVar v) = bind v t
unifies t1@(t11 `TApp` t12) t2@(t21 `TApp` t22)
  -- The root of a type application must be a fixed constructor, not a type
  -- variable. I'm not entirely sure why, and may just remove this restriction
  -- in future.
  | isTVar t11 || isTVar t21
  = Left $ "Root must be fixed constructor. Got: " <> tshow (t1, t2)
  | otherwise = unifiesMany [t11, t12] [t21, t22]
  where isTVar = \case { TVar _ -> True; TCon _ -> False; TApp _ _ -> False }
unifies a b = Left $ "unification fail: " <> tshow a <> " is not " <> tshow b

unifiesMany :: [MType Tc] -> [MType Tc] -> Solve Subst
unifiesMany [] [] = return nullSubst
unifiesMany (t1 : ts1) (t2 : ts2) = do
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
