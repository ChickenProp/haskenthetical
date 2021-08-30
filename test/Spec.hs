{-# OPTIONS_GHC -Wno-orphans #-}

import Prelude.Extra

import qualified Control.Exception as E
import Data.List.Split (splitWhen)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Test.Hspec
import Text.InterpolatedString.Perl6 (qc)

import App
import Env
import Eval
import Parser
import Syntax
import TypeCheck

-- | This is only partial equality, so don't implement it in the main codebase.
instance Eq Val where
  Literal l1 == Literal l2 = l1 == l2
  Tag n1 vs1 == Tag n2 vs2 = n1 == n2 && vs1 == vs2
  _ == _ = False

main :: IO ()
main = hspec $ do
  describe "From tests.hts" $ do
    allTestContents <- runIO $ readFile "test/tests.hts"
    -- Annotate each line with the number of the one before. Then the first line
    -- in a group has the line number of the `# # #`.
    let eachTestContents :: [(Int, String)] =
          mapMaybe
            (\case
              [] -> Nothing
              l@((n, _):_) -> Just (n, unlines $ snd <$> l)
            )
            $ splitWhen (("# # #" ==) . snd)
            $ zip [0..] (lines allTestContents)

    let treeses :: [(Int, Either CompileError [SyntaxTree])] =
          second (parseWholeFile "<src>") <$> eachTestContents

    forM_ treeses $ \(lineNo, trees) -> case trees of
      Left err ->
        it [qc|Parse error at L{lineNo}|] $
          expectationFailure $ Text.unpack $ ppCompileError err
      Right [] -> return ()
      Right [STTree (STBare testFunc : args)] ->
        it [qc|{testFunc} at L{lineNo}|] $ runHtsTest testFunc args
      Right _ ->
        it [qc|Malformed test at L{lineNo}|] $
          expectationFailure "Malformed test"

  describe "Sanity checking" $ do
    it "Can test MTypes for equivalence" $ do
      let testEquiv a b =
            if mtypesEquiv a b
              then return ()
              else expectationFailure [qc|{a} is not equivalent to {b}|]
          testNotEquiv a b =
            if mtypesEquiv a b
              then expectationFailure [qc|{a} is equivalent to {b}|]
              else return ()

      let h = HType
          tc, tv :: Kind -> Name -> MType Tc
          tc k x = TCon $ TC k x
          tv k x = TVar $ TV k x
          func :: MType Tc -> MType Tc -> MType Tc
          func a b = TApp (TApp (tc (h :*-> h :*-> h) "->") a) b

      testEquiv (tc h "a") (tc h "a")
      testNotEquiv (tc h "a") (tc h "b")
      testNotEquiv (tc (h :*-> h) "a") (tc h "a")

      testEquiv (tv h "a") (tv h "a")
      testEquiv (tv h "a") (tv h "b")
      testNotEquiv (tv (h :*-> h) "a") (tv h "b")

      -- These need the @[] because OverloadedLists confuses type inference.
      forM_ @[] [ (\a b -> TApp (tc (h :*-> h) a) (tc h b))
                , (\a b -> func (tc h a) (tc h b))
                ] $ \tctc -> do
        testEquiv (tctc "a" "b") (tctc "a" "b")
        testNotEquiv (tctc "a" "b") (tctc "a" "c")
        testNotEquiv (tctc "a" "b") (tctc "c" "b")

      forM_ @[] [ (\a b -> TApp (tc (h :*-> h) a) (tv h b))
                , (\a b -> func (tc h a) (tv h b))
                ] $ \tctv -> do
        testEquiv (tctv "a" "b") (tctv "a" "b")
        testEquiv (tctv "a" "b") (tctv "a" "c")
        testNotEquiv (tctv "a" "b") (tctv "c" "b")

      forM_ @[] [ (\a b -> TApp (tv (h :*-> h) a) (tc h b))
                , (\a b -> func (tv h a) (tc h b))
                ] $ \tvtc -> do
        testEquiv (tvtc "a" "b") (tvtc "a" "b")
        testEquiv (tvtc "a" "b") (tvtc "c" "b")
        testNotEquiv (tvtc "a" "b") (tvtc "a" "c")

      forM_ @[] [ (\a b -> TApp (tv (h :*-> h) a) (tv h b))
                , (\a b -> func (tv h a) (tv h b))
                ] $ \tvtv -> do
        testEquiv (tvtv "a" "b") (tvtv "a" "b")
        testEquiv (tvtv "a" "b") (tvtv "c" "b")
        testEquiv (tvtv "a" "b") (tvtv "a" "c")
        testEquiv (tvtv "a" "b") (tvtv "c" "d")

-- | Check that two MTypes are the same up to renaming variables. This is a
-- stricter condition than checking that they Unify, or even that one Matches
-- the other. It's equivalent to specifying that both of them Match the other.
mtypesEquiv :: MType Tc -> MType Tc -> Bool
mtypesEquiv m1 m2 =
  -- We could also check `solver1 [Match m1 m2]` and `solver1 [Match m2 m1]`.
  -- (Can't do both those constraints at once, because solving one constraint
  -- applies substitutions when solving the other.) But that currently can't
  -- handle type variables at the root of an application. We don't currently
  -- construct any examples of that, but if we do in future we want to already
  -- be testing it.
  (Set.size (ftv m1) == Set.size (ftv m2))
    && either (const False) (const True) (go Map.empty m1 m2)
 where
  -- Walk the tree. If we see two TVars, record that the left one must always be
  -- paired with the right one going forwards. This makes sure that (if `go`
  -- ultimately succeeds) the mapping left -> right is a function. We know it's
  -- surjective because every TVar on the right is paired with a TVar on the
  -- left; then it must also be injective because the sets have the same size.
  -- So we have a bijection. No need to also record the right -> left mapping.
  go :: acc ~ Map (TVar Tc) (TVar Tc)
     => acc -> MType Tc -> MType Tc -> Either () acc
  go acc (TApp m11 m12) (TApp m21 m22) = do
    acc' <- go acc m11 m21
    go acc' m12 m22
  go acc (TCon c1) (TCon c2) = if c1 == c2 then Right acc else Left ()
  go acc (TVar v1) (TVar v2) = do
    when (getKind v1 /= getKind v2) $ Left ()
    case Map.lookup v1 acc of
      Nothing -> Right $ Map.insert v1 v2 acc
      Just v2' -> if v2 == v2' then Right acc else Left ()
  go _ _ _ = Left ()

runHtsTest :: Text -> [SyntaxTree] -> IO ()
runHtsTest testFunc args = do
  case Map.lookup testFunc testFuncs of
    Nothing -> error [qc|No test function {testFunc}|]
    Just f -> f args
 where
  testFuncs = Map.fromList
    [ ("has-type", testHasType)
    , ("returns", testReturns)
    , ("compile-fails-with", testCompileFailsWith)
    , ("eval-fails-with", testEvalFailsWith)
    , ("pending", testPending)
    ]

testHasType :: [SyntaxTree] -> IO ()
testHasType [] = error "has-type needs args"
testHasType (expectedType : testExprs) = do
  (actualPType, tyEnv) <-
    case runSilentApp $ compileProgramFromTrees testExprs of
      Left err -> error $ Text.unpack $ ppCompileError err
      Right (ty, env, _) -> return (ty, feTypes env)
  let psExpectedType =
        either (error . Text.unpack) id $ parseMType expectedType
      tcExpectedType = either (error . Text.unpack . ppCompileError) id
        $ ps2tc_MType tyEnv psExpectedType

  when (ftv actualPType /= []) $
    expectationFailure "Result of type checking has free type variables"

  let Forall _ actualMType = actualPType
  if mtypesEquiv tcExpectedType actualMType
    then return ()
         -- shouldBe is too strict, but we know it fails and there's no easy way
         -- to format a custom error message nicely.
    else actualMType `shouldBe` tcExpectedType

testReturns :: [SyntaxTree] -> IO ()
testReturns [] = error "returns needs args"
testReturns (expectedValTree : testExprs) = do
  let fakeEvalTree = \case
        STFloat x -> Literal $ Float x
        STString x -> Literal $ String x
        STBare x -> Tag (Name x) []
        STTree (STBare hd : rest) -> Tag (Name hd) $ fakeEvalTree <$> rest
        STTree _ -> error "bad fake eval"
  case runSilentApp $ compileProgramFromTrees testExprs of
    Left err -> error $ Text.unpack $ ppCompileError err
    Right (_, env, expr) -> case eval1 (getSymbols env) expr of
      Left err -> error $ Text.unpack err
      Right val -> val `shouldBe` fakeEvalTree expectedValTree

testCompileFailsWith :: [SyntaxTree] -> IO ()
testCompileFailsWith (STBare failure : testExprs) =
  case runSilentApp $ compileProgramFromTrees testExprs of
    Left err -> show err `shouldStartWith` Text.unpack failure
    Right _ -> expectationFailure "Compilation didn't fail"
testCompileFailsWith _ = error "malformed compile-fails-with"

testEvalFailsWith :: [SyntaxTree] -> IO ()
testEvalFailsWith (STString failure : testExprs) =
  case runSilentApp $ compileProgramFromTrees testExprs of
    Left err -> error $ Text.unpack $ ppCompileError err
    Right (_, env, expr) -> case eval1 (getSymbols env) expr of
      Left err -> err `shouldBe` failure
      Right _ -> expectationFailure "Evaluation didn't fail"
testEvalFailsWith _ = error "malformed eval-fails-with"

-- | Make sure pending tests actually do fail, so we don't forget to update them
-- if we make them work.
testPending :: [SyntaxTree] -> IO ()
testPending [STString reason, STTree (STBare testFunc : args)] =
  E.try (runHtsTest testFunc args) >>= \case
    Left (_ :: E.SomeException) -> pendingWith $ Text.unpack reason
    Right () -> expectationFailure "Pending test actually succeeded"
testPending _ = error "malformed pending"
