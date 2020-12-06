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
import qualified Data.TreeDiff as TD

import Env
import Syntax
import Gist

data Constraint
  = Unify (MType Tc) (MType Tc)
  -- ^ These two types must be "the same". That is, we can create a substitution
  -- `s` such that `apply s t1 = apply s t2`.
  | Match (MType Tc) (MType Tc)
  -- ^ These two types must be "the same", but also, t1 must be a specialization
  -- of t2. That is, we can create a substitution `s` such that `apply s t2 = t1`.
  deriving (Show)
instance Gist Constraint where
  gist = \case
    Unify a b -> TD.App "Unify" [gist a, gist b]
    Match a b -> TD.App "Match" [gist a, gist b]

insertMany :: Ord k => [(k, v)] -> Map k v -> Map k v
insertMany bs m = Map.union (Map.fromList bs) m

extending :: Name -> PType Tc -> Infer a -> Infer a
extending n t m = local (field @"ieVars" %~ Map.insert n t) m

newtype Subst = Subst { _subst :: Map (TVar Tc) (MType Tc) }
  deriving (Eq, Show, Gist)

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
  apply s (Unify t1 t2) = Unify (apply s t1) (apply s t2)
  apply s (Match t1 t2) = Match (apply s t1) (apply s t2)
  ftv (Unify t1 t2) = ftv t1 `Set.union` ftv t2
  ftv (Match t1 t2) = ftv t1 `Set.union` ftv t2

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

-- | Instantiate a PType into an MType.
--
-- For each TVar listed in the Forall, we generate a fresh gensym and substitute
-- it into the main type.
instantiate :: PType Tc -> Infer (MType Tc)
instantiate (Forall as t) = do
  as' <- mapM (const genSym) as
  let subst = Subst $ Map.fromList (zip as as')
  return $ apply subst t

-- | Generalize an MType into a PType.
--
-- Any type variables mentioned in the MType, but not found in the environment,
-- get placed into the Forall.
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
unify t1 t2 = tell [Unify t1 t2]

ps2tc_Infer :: PType Ps -> Infer (PType Tc)
ps2tc_Infer t = do
  env <- asks ieTypes
  lift $ ps2tc_PType (Forall [] <$> env) t

inferTypedOn :: (b -> MType Tc) -> (a -> Infer b) -> Typed a -> Infer b
inferTypedOn _ f (UnTyped e) = f e
inferTypedOn getType f (Typed t e) = do
  t' <- instantiate =<< ps2tc_Infer t
  e' <- f e
  tell [Match t' (getType e')]
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
    let (declaredType, bindingName) = extractType x
    argType <- maybe genSym (instantiate <=< ps2tc_Infer) declaredType
    t <- extending bindingName (Forall [] argType) (inferTypedExpr e)
    return $ argType +-> t

  Let [] e -> inferTypedExpr e
  Let (b1:bs) e -> do
    env <- asks ieVars

    let (extractType -> (declaredType, bindingName), boundExpr) = b1
    (inferredType, constraints) <- listen $ do
      inferTyped inferTypedExpr (mkTyped declaredType boundExpr)

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
        t1 <- local (field @"ieVars" %~ insertMany tBindings) $ do
                let e1TypedTwice = mkTyped (fst $ extractType n1) e1
                inferTyped inferTypedExpr e1TypedTwice
        unify tv t1
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

-- | Subst that binds variable a to type t
bind :: TVar Tc -> MType Tc -> Solve Subst
bind a t | t == TVar a = return nullSubst
         | a `Set.member` ftv t = Left $ CEInfiniteType t
         | otherwise = return $ Subst $ Map.singleton a t

constrain :: Bool -> MType Tc -> MType Tc -> Solve Subst
constrain twoWay = go
 where
  go t1 t2
    | t1 == t2 = return nullSubst
    | getKind t1 /= getKind t2 = Left $ CEKindMismatch t1 t2
  go t (TVar v) = bind v t
  go t1@(TVar v) t2 =
    if twoWay then bind v t2 else Left $ CEDeclarationTooGeneral t1 t2
  go t1@(t11 `TApp` t12) t2@(t21 `TApp` t22)
    -- The root of a type application must be a fixed constructor, not a type
    -- variable. I'm not entirely sure why, and may just remove this restriction
    -- in future. Would probably need `ps2tc_PType` and `ps2tc_MType` to be able
    -- to construct a TVar with a kind other than HType.
    | isTVar t11 = Left $ CETVarAsRoot t1
    | isTVar t21 = Left $ CETVarAsRoot t2
    | otherwise = do
        sl <- go t11 t21
        sr <- go (apply sl t12) (apply sl t22)
        return $ sr `composeSubst` sl
    where isTVar = \case { TVar _ -> True; TCon _ -> False; TApp _ _ -> False }
  go a b = Left $ CEUnificationFail a b

solver :: Unifier -> Solve Subst
solver (su, cs) =
 case cs of
   [] -> return su
   (Unify t1 t2 : cs0) -> do
     su1 <- constrain True t1 t2
     solver (su1 `composeSubst` su, apply su1 cs0)
   (Match t1 t2 : cs0) -> do
     su1 <- constrain False t1 t2
     when (apply su1 t2 /= t1) $ Left $ CEDeclarationTooGeneral t1 t2
     solver (su1 `composeSubst` su, apply su1 cs0)

solver1 :: [Constraint] -> Solve Subst
solver1 cs = solver (nullSubst, cs)

-- | Subst that applies s2 followed by s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s1@(Subst s1') (Subst s2') =
  Subst $ fmap (apply s1) s2' `Map.union` s1'
