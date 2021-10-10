module TypeCheck
  ( runTypeCheck
  , typeCheckDefs
  , typeCheckMacs

  -- Currently only exported for testing
  , Constraint(..)
  , Substitutable(..)
  , generalize
  , solver1
  ) where

import Prelude.Extra

import Control.Monad (replicateM, zipWithM)
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
  -- of t2. That is, we can create a substitution `s` such that
  -- `apply s t2 = t1`.
  --
  --     g <- genSym
  --     Match tString g -- this is fine, will substitute g -> String
  --                     -- going forward.
  --     Match g tString -- this will throw an error.
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
  apply s@(Subst s') = \case
    TCon a           -> TCon a
    t@(TVar a)       -> Map.findWithDefault t a s'
    t1 `TApp` t2     -> apply s t1 `TApp` apply s t2
    MacroMType v _ _ -> absurd v

  ftv = \case
    TCon _           -> Set.empty
    TVar a           -> Set.singleton a
    t1 `TApp` t2     -> ftv t1 `Set.union` ftv t2
    MacroMType v _ _ -> absurd v

instance Substitutable (PType Tc) where
  apply (Subst s) (Forall as t) =
    Forall as $ apply (Subst $ foldr Map.delete s as) t
  apply _ (MacroPType v _ _) = absurd v
  ftv (Forall as t) = ftv t `Set.difference` as
  ftv (MacroPType v _ _) = absurd v

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

runTypeCheck
  :: InferEnv
  -> Typed Me (Expr Me)
  -> Either CompileError (PType Tc, Typed Tc (Expr Tc))
runTypeCheck env expr = do
  when (not $ Set.null $ ftv $ ieVars env) $ do
    Left $ CECompilerBug "Free type vars in environment"

  ((ty, expr'), _, constraints)
    <- runRWST (inferTypedExpr expr) env (InferState letters)
  subst <- solver1 constraints
  return (generalize Map.empty $ apply subst ty, expr')
 where
  letters :: [TVar Tc]
  letters =
    map (TV HType . Name . Text.pack) $ [1..] >>= flip replicateM ['a'..'z']

typeCheckDefs
  :: InferEnv
  -> [(Typed Me Name, Typed Me (Expr Me))]
  -> Either CompileError [(Name, PType Tc, Typed Tc (Expr Tc))]
typeCheckDefs env defs = do
  ((inferredTypes, inferredExprs), _, _)
    <- runRWST (inferRecBindings defs) env (InferState letters)
  -- Should be no need for constraint solving or generalization here, because
  -- `inferRecBindings` does those.
  return $ zipWith (\(n, t) (_, e) -> (n, t, e)) inferredTypes inferredExprs
 where
  letters :: [TVar Tc]
  letters =
    map (TV HType . Name . Text.pack) $ [1..] >>= flip replicateM ['a'..'z']

typeCheckMacs
  :: InferEnv
  -> [(Name, Typed Me (Expr Me))]
  -> Either CompileError [(Name, Expr Tc)]
typeCheckMacs env defs = do
  (inferredExprs, _, constraints) <- runRWST go env (InferState letters)
  -- We know exactly what type we have, so there's no need to do substitution or
  -- generalization. But by running the solver we verify that we actually do
  -- have that type.
  void $ solver1 constraints
  return inferredExprs
 where
  letters :: [TVar Tc]
  letters =
    map (TV HType . Name . Text.pack) $ [1..] >>= flip replicateM ['a'..'z']
  go = do
    forM defs $ \(name , expr) -> do
      (ty, expr') <- inferTypedExpr expr
      unify ty $ tList tSyntaxTree +-> tSyntaxTree
      return (name, rmType expr')

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
instantiate (MacroPType v _ _) = absurd v
instantiate (Forall (Set.toList -> as) t) = do
  as' <- mapM (const genSym) as
  let subst = Subst $ Map.fromList (zip as as')
  return $ apply subst t

-- | Generalize an MType into a PType.
--
-- Any type variables mentioned in the MType, but not found in the environment,
-- get placed into the Forall.
generalize :: TypeEnv PType -> MType Tc -> PType Tc
generalize env t = Forall as t
  where as = ftv t `Set.difference` ftv env

lookupVar :: Name -> Infer (MType Tc)
lookupVar n = do
  env <- asks ieVars
  case env !? n of
    Nothing -> lift $ Left $ CEUnboundVar n
    Just t -> instantiate t

unify :: MType Tc -> MType Tc -> Infer ()
unify t1 t2 = tell [Unify t1 t2]

me2tc_Infer :: PType Me -> Infer (PType Tc)
me2tc_Infer t = do
  env <- asks ieTypes
  lift $ me2tc_PType (Forall [] <$> env) t

me2tc_InferMay :: Maybe (PType Me) -> Infer (Maybe (PType Tc))
me2tc_InferMay Nothing = pure Nothing
me2tc_InferMay (Just t) = Just <$> me2tc_Infer t

me2tc_InferTyped :: Typed Me a -> Infer (Typed Tc a)
me2tc_InferTyped x = let (t, a) = extractType x
                     in mkTyped <$> me2tc_InferMay t <*> pure a

-- | Run inference on a typed value. `f` runs it on the value, and if there's a
-- type, it's matched with the result of `getType` on the result of `f`.
inferTypedOn :: (b -> MType Tc) -> (a -> Infer b) -> Typed Me a -> Infer b
inferTypedOn _ f (UnTyped e) = f e
inferTypedOn getType f (Typed t e) = do
  t' <- instantiate =<< me2tc_Infer t
  e' <- f e
  tell [Match t' (getType e')]
  return e'

inferTypedExpr :: Typed Me (Expr Me) -> Infer (MType Tc, Typed Tc (Expr Tc))
inferTypedExpr te = do
  let (t, _) = extractType te
  t' <- me2tc_InferMay t
  fmap (mkTyped t') <$> inferTypedOn fst inferExpr te

inferLiteral :: Literal -> Infer (MType Tc)
inferLiteral = return . \case
    Float _ -> tFloat
    String _ -> tString

-- | This both checks the type and switches up the Pass from Me to Tc. As of
-- writing, the Pass change is completely straightforward, and it might make
-- more sense to do it separately. But it feels likely to be less
-- straightforward in future, and to need info from typechecking, so here we
-- are.
inferExpr :: Expr Me -> Infer (MType Tc, Expr Tc)
inferExpr expr = case expr of
  Val (Literal l) -> (, Val (Literal l)) <$> inferLiteral l
  Val v -> error $ "unexpected Val during typechecking: " ++ show v

  Var n -> (, Var n) <$> lookupVar n

  Lam x e -> do
    let (declaredType, bindingName) = extractType x
    x' <- me2tc_InferTyped x
    argType <- maybe genSym (instantiate <=< me2tc_Infer) declaredType
    (t, e') <- extending bindingName (Forall [] argType) (inferTypedExpr e)
    return (argType +-> t, Lam x' e')

  Let bindings e -> go [] bindings
   where
    go bindings' [] = fmap (Let $ reverse bindings') <$> inferTypedExpr e
    go bindings' (b1:bs) = do
      env <- asks ieVars

      let (tBindingName, boundExpr) = b1
          (declaredType, bindingName) = extractType tBindingName
      tBindingName' <- me2tc_InferTyped tBindingName

      ((inferredType, boundExpr'), constraints) <- listen $ do
        inferTypedOn fst inferTypedExpr (mkTyped declaredType boundExpr)

      subst <- liftEither $ solver1 constraints
      let gen = generalize env (apply subst inferredType)
      extending bindingName gen $ go ((tBindingName', boundExpr'):bindings') bs

  LetRec bindings e -> do
    (gens, bindings') <- inferRecBindings bindings
    (t, e') <- local (field @"ieVars" %~ insertMany gens) $ inferTypedExpr e

    return (t, LetRec bindings' e')

  Call fun a -> do
    (t1, fun') <- inferTypedExpr fun
    (t2, a') <- inferTypedExpr a
    tv <- genSym
    unify t1 (t2 +-> tv)
    return (tv, Call fun' a')

  IfMatch inE pat thenE elseE -> do
    (inT, inE') <- inferTypedExpr inE
    (pat', patBindings) <- inferPat inT pat

    (thenT, thenE') <- local (field @"ieVars" %~ insertMany patBindings)
                   (inferTypedExpr thenE)
    (elseT, elseE') <- inferTypedExpr elseE

    unify thenT elseT

    return (thenT, IfMatch inE' pat' thenE' elseE')

  MacroExpr v _ _ -> absurd v

inferRecBindings
  :: [(Typed Me Name, Typed Me (Expr Me))]
  -> Infer ( [(Name, PType Tc)]
           , [(Typed Tc Name, Typed Tc (Expr Tc))]
           )
inferRecBindings bindings = do
  env <- asks ieVars

  -- Every binding gets a unique genSym, which we unify with its declared type
  -- if any. For each expr, we infer its type given that the other names have
  -- those genSyms. Then we unify its inferred type with its own genSym.

  genSyms <- forM bindings $ \_ -> genSym

  let tBindings = flip map (zip genSyms bindings) $ \(tv, (n, _)) ->
        (rmType n, Forall [] tv)
  (inferredTypesAndBindings, constraints) <-
    listen $ forM (zip genSyms bindings) $ \(tv, (n1, e1)) -> do
      n1' <- me2tc_InferTyped n1
      (t1, e1') <- local (field @"ieVars" %~ insertMany tBindings) $ do
        let e1TypedTwice = mkTyped (fst $ extractType n1) e1
        inferTypedOn fst inferTypedExpr e1TypedTwice
      unify tv t1
      return (t1, (n1', e1'))
  let (inferredTypes, bindings') = unzip inferredTypesAndBindings

  subst <- liftEither $ solver1 constraints
  let gens = flip map (zip bindings inferredTypes) $ \((n, _), t1) ->
        (rmType n, generalize env (apply subst t1))

  return (gens, bindings')

inferPat
  :: MType Tc
  -> Typed Me (Pattern Me)
  -> Infer (Typed Tc (Pattern Tc), [(Name, PType Tc)])
inferPat inT inTPat = withT =<< case inPat of
  PatLiteral l -> do
    t <- inferLiteral l
    unify t inT
    return (t, PatLiteral l, [])
  PatVal n -> do
    return (inT, PatVal n, [(n, Forall [] inT)])
  PatConstr conName pats -> do
    pTypes <- traverse (\_ -> genSym) pats

    env <- asks ieVars
    case env !? conName of
      Nothing -> lift $ Left $ CEUnboundVar conName
      Just conPType -> do
        conMType <- instantiate conPType
        unify conMType $ foldr (+->) inT pTypes

    -- When a pattern has a type signature, The Match from `inferTypedOn` has to
    -- happen *after* we unify inT with the pattern type. Otherwise the type
    -- matched against won't be sufficiently known, and we won't constrain it.
    --
    -- This isn't fully effective. E.g.
    --
    --     (if~ 3 (: $x $a) x ...) # fails as expected
    --     (if~ n (: $x $a) (+ x 1) ...) # should fail, doesn't
    --     (+ 1 (if~ n (: $x $a) x ...)) # should fail, doesn't
    --
    -- We might need to implement constraints to get those others to work, and
    -- when we do, it shouldn't be necessary to pass `inT` in to this function
    -- any more.
    --
    -- Discussion: https://www.reddit.com/r/ProgrammingLanguages/comments/k7cj7e

    (pats', bindings) <-
      unzip <$> zipWithM (\pat pType -> inferPat pType pat) pats pTypes

    return (inT, PatConstr conName pats', concat bindings)
  where
    inPat = rmType inTPat
    withT (outT, outPat, bindings) = case inTPat of
      UnTyped _ -> pure $ (UnTyped outPat, bindings)
      Typed t _ -> do
        t' <- me2tc_Infer t
        t'' <- instantiate t'
        tell [Match t'' outT]
        return (Typed t' outPat, bindings)

---

type Unifier = (Subst, [Constraint])
type Solve a = Either CompileError a

-- | Subst that binds variable a to type t
bind :: TVar Tc -> MType Tc -> Solve Subst
bind a t | t == TVar a = return nullSubst
         | a `Set.member` ftv t = Left $ CEInfiniteType a t
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
    -- in future. Would probably need `me2tc_PType` and `me2tc_MType` to be able
    -- to construct a TVar with a kind other than HType.
    | isTVar t11 = Left $ CETVarAsRoot t1
    | isTVar t21 = Left $ CETVarAsRoot t2
    | otherwise = do
        sl <- go t11 t21
        sr <- go (apply sl t12) (apply sl t22)
        return $ sr `composeSubst` sl
    where isTVar = \case
            TVar _ -> True
            TCon _ -> False
            TApp _ _ -> False
            MacroMType v _ _ -> absurd v
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
