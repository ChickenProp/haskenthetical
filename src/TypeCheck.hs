module TypeCheck
  ( runTypeCheck
  ) where

import Prelude.Extra

import Control.Monad (replicateM)
import Control.Monad.Except (liftEither)
import Control.Monad.Trans (lift)
import Control.Monad.RWS.Strict
  (RWST, runRWST, tell, local, get, put, asks, listen)
import qualified Data.Map.Strict as Map
import Data.Map.Strict ((!?))
import qualified Data.Set as Set
import qualified Data.Text as Text

import Env
import Syntax

type Constraint = (MType Tc, MType Tc)

insertMany :: Ord k => [(k, v)] -> Map k v -> Map k v
insertMany bs m = Map.union (Map.fromList bs) m

extending :: Name -> PType Tc -> Infer a -> Infer a
extending n t m = local (field @"ieVars" %~ Map.insert n t) m

newtype Subst = Subst { _subst :: Map (TVar Tc) (MType Tc) }
  deriving (Eq, Show)

nullSubst :: Subst
nullSubst = Subst Map.empty

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set (TVar Tc)

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

instance Substitutable v => Substitutable (Map k v) where
  apply s m = apply s <$> m
  ftv m = ftv $ Map.elems m


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
--
-- (Of course, we also need to make sure the solver *knows* about this
-- unification. Meaning we need to do it inside of a `listen`, not outside.)

runTypeCheck :: InferEnv -> Typed Expr -> Either CompileError (PType Tc)
runTypeCheck env expr = do
  (ty, _, constraints) <- runRWST (inferTypedExpr expr) env (InferState letters)
  subst <- solver1 constraints
  return $ generalize (ieVars env) $ apply subst ty
 where
  letters :: [TVar Tc]
  letters =
    map (TV HType . Name . Text.pack) $ [1..] >>= flip replicateM ['a'..'z']

---

data InferState = InferState { _vars :: [TVar Tc] }
type Infer a = RWST InferEnv [Constraint] InferState (Either CompileError) a

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

generalize :: TypeEnv PType -> MType Tc -> PType Tc
generalize env t = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env

lookupVar :: Name -> Infer (MType Tc)
lookupVar n = do
  env <- asks ieVars
  case env !? n of
    Nothing -> lift $ Left $ CEUnboundVar n
    Just t -> instantiate t

unify :: MType Tc -> MType Tc -> Infer ()
unify t1 t2 = tell [(t1, t2)]

ps2tc_Infer :: PType Ps -> Infer (PType Tc)
ps2tc_Infer t = do
  env <- asks ieTypes
  lift $ ps2tc_PType (Forall [] <$> env) t

inferTypedOn :: (b -> MType Tc) -> (a -> Infer b) -> Typed a -> Infer b
inferTypedOn _ f (UnTyped e) = f e
inferTypedOn getType f (Typed t e) = do
  t' <- instantiate =<< ps2tc_Infer t
  e' <- f e
  unify t' (getType e')
  return e'

inferTyped :: (a -> Infer (MType Tc)) -> Typed a -> Infer (MType Tc)
inferTyped = inferTypedOn id

inferTypedExpr :: Typed Expr -> Infer (MType Tc)
inferTypedExpr = inferTyped inferExpr

inferLiteral :: Literal -> Infer (MType Tc)
inferLiteral = return . \case
    Float _ -> tFloat
    String _ -> tString

inferExpr :: Expr -> Infer (MType Tc)
inferExpr expr = case expr of
  Val (Literal l) -> inferLiteral l
  Val v -> error $ "unexpected Val during typechecking: " ++ show v

  Var n -> lookupVar n

  Lam x e -> do
    tv <- genSym
    t <- extending (rmType x) (Forall [] tv) (inferTypedExpr e)
    return $ tv +-> t

  Let [] e -> inferTypedExpr e
  Let (b1:bs) e -> do
    env <- asks ieVars

    let (extractType -> (declaredType, bindingName), boundExpr) = b1
    (inferredType, constraints) <- listen $ do
      inferredType <- inferTypedExpr boundExpr
      whenJust declaredType $ \t ->
        unify inferredType =<< instantiate =<< ps2tc_Infer t
      return inferredType

    subst <- liftEither $ solver1 constraints
    let gen = generalize env (apply subst inferredType)
    extending bindingName gen (inferExpr $ Let bs e)

  LetRec bindings e -> do
    env <- asks ieVars

    -- Every binding gets a unique genSym, which we unify with its declared type
    -- if any. For each expr, we infer its type given that the other names have
    -- those genSyms. Then we unify its inferred type with its own genSym.

    genSyms <- forM bindings $ \_ -> genSym

    let tBindings = flip map (zip genSyms bindings) $ \(tv, (n, _)) ->
          (rmType n, Forall [] tv)
    (inferredTypes, constraints) <- listen $ forM (zip genSyms bindings)
      $ \(tv, (n1, e1)) -> do
        t1 <- local (field @"ieVars" %~ insertMany tBindings)
                    (inferTypedExpr e1)
        unify tv t1
        whenJust (fst $ extractType n1) $ \t1' ->
          unify tv =<< instantiate =<< ps2tc_Infer t1'
        return t1

    subst <- liftEither $ solver1 constraints
    let gens = flip map (zip bindings inferredTypes) $ \((n, _), t1) ->
          (rmType n, generalize env (apply subst t1))
    seq gens $ local (field @"ieVars" %~ insertMany gens) $ inferTypedExpr e

  Call fun a -> do
    t1 <- inferTypedExpr fun
    t2 <- inferTypedExpr a
    tv <- genSym
    unify t1 (t2 +-> tv)
    return tv

  IfMatch inE pat thenE elseE -> do
    inT <- inferTypedExpr inE
    (patT, patBindings) <- inferTypedOn fst inferPat pat
    thenT <- local (field @"ieVars" %~ insertMany patBindings)
                   (inferTypedExpr thenE)
    elseT <- inferTypedExpr elseE

    unify inT patT
    unify thenT elseT

    return thenT

inferPat :: Pattern -> Infer (MType Tc, [(Name, PType Tc)])
inferPat = \case
  PatLiteral l -> (, []) <$> inferLiteral l
  PatVal n -> do
    t <- genSym
    return (t, [(n, Forall [] t)])
  PatConstr conName pats -> do
    (pTypes, bindings) <- unzip <$> traverse (inferTypedOn fst inferPat) pats
    t <- genSym

    env <- asks ieVars
    case env !? conName of
      Nothing -> lift $ Left $ CEUnboundVar conName
      Just conPType -> do
        conMType <- instantiate conPType
        unify conMType $ foldr (+->) t pTypes

    return (t, concat bindings)

---

type Unifier = (Subst, [Constraint])
type Solve a = Either CompileError a

-- | Subst that applies s2 followed by s1
compose :: Subst -> Subst -> Subst
s1@(Subst s1') `compose` (Subst s2') =
  Subst $ fmap (apply s1) s2' `Map.union` s1'

-- | Subst that binds variable a to type t
bind :: TVar Tc -> MType Tc -> Solve Subst
bind a t | t == TVar a = return nullSubst
         | a `Set.member` ftv t = Left $ CEInfiniteType t
         | otherwise = return $ Subst $ Map.singleton a t

unifies :: MType Tc -> MType Tc -> Solve Subst
unifies t1 t2
  | t1 == t2 = return nullSubst
  | getKind t1 /= getKind t2
    = Left $ CEKindMismatch t1 t2
unifies (TVar v) t = bind v t
unifies t (TVar v) = bind v t
unifies t1@(t11 `TApp` t12) t2@(t21 `TApp` t22)
  -- The root of a type application must be a fixed constructor, not a type
  -- variable. I'm not entirely sure why, and may just remove this restriction
  -- in future.
  | isTVar t11 = Left $ CETVarAsRoot t1
  | isTVar t21 = Left $ CETVarAsRoot t2
  | otherwise = unifiesMany [t11, t12] [t21, t22]
  where isTVar = \case { TVar _ -> True; TCon _ -> False; TApp _ _ -> False }
unifies a b = Left $ CEUnificationFail a b

unifiesMany :: [MType Tc] -> [MType Tc] -> Solve Subst
unifiesMany [] [] = return nullSubst
unifiesMany (t1 : ts1) (t2 : ts2) = do
  su1 <- unifies t1 t2
  su2 <- unifiesMany (apply su1 ts1) (apply su1 ts2)
  return (su2 `compose` su1)
unifiesMany _ _ = Left $ CECompilerBug "unification mismatch"

solver :: Unifier -> Solve Subst
solver (su, cs) =
 case cs of
   [] -> return su
   ((t1, t2) : cs0) -> do
     su1 <- unifies t1 t2
     solver (su1 `compose` su, apply su1 cs0)

solver1 :: [Constraint] -> Solve Subst
solver1 cs = solver (nullSubst, cs)
