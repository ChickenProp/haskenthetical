{-# OPTIONS_GHC -Wno-orphans #-}

import Prelude.Extra

import qualified Control.Exception as E
import Data.List.Split (splitWhen)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Test.Hspec
import Text.InterpolatedString.Perl6 (qc)

import App
import Env
import Eval
import Parser
import Syntax

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
  (actualType, tyEnv) <-
    case runSilentApp $ compileProgramFromTrees testExprs of
      Left err -> error $ Text.unpack $ ppCompileError err
      Right (ty, env, _) -> return (ty, feTypes env)
  let psExpectedType =
        either (error . Text.unpack) id $ parseMType expectedType
      tcExpectedType = either (error . Text.unpack . ppCompileError) id
        $ ps2tc_MType tyEnv psExpectedType

  actualType `shouldBe` Forall [] tcExpectedType

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
