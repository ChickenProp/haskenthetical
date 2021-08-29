{-# OPTIONS_GHC -Wno-orphans #-}

import Prelude.Extra

import qualified Control.Exception as E
import Data.List.Split (splitWhen)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Test.Hspec
import Text.InterpolatedString.Perl6 (q, qc)

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

runEval :: String -> Either Text Val
runEval program = do
  (_, env, expr) <- first tshow $ runSilentApp $ compileProgram "<str>" program
  eval1 (getSymbols env) expr

main :: IO ()
main = hspec $ do
  let vFloat = Literal . Float
      vString = Literal . String

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

  describe "Evaluation" $ do
    let returns :: String -> Val -> Expectation
        prog `returns` v = runEval prog `shouldBe` Right v

        failsWith :: String -> Text -> Expectation
        prog `failsWith` e = runEval prog `shouldBe` Left e

    it "evals constants" $ do
      "3" `returns` vFloat 3
      [q|"foo"|] `returns` vString "foo"

    it "performs arithmetic" $ do
      "(+ 3 4)" `returns` vFloat 7
      "(+ 3 (+ 4 5))" `returns` vFloat 12
      "(+ (+ 3 4) 5)" `returns` vFloat 12
      "(+ (+ 3.2 4.1) 5.3)" `returns` vFloat 12.6
      "(- 3 4)" `returns` vFloat (-1)
      "(* 7.2 3.1)" `returns` vFloat 22.32

    it "factorial" $ do
      [q|(letrec ((fac (λ x (if~ x 0 1 (* x (fac (- x 1)))))))
           (fac 3))|] `returns` vFloat 6
      [q|(def fac (λ x (if~ x 0 1 (* x (fac (- x 1))))))
         (fac 3)|] `returns` vFloat 6

    it "letrec" $ do
      [q|(letrec ((id (λ x x))
                  (f (elim-+ id g))
                  (g (λ x (f (Left x)))))
             (f (Right 3)))|]
        `returns` vFloat 3
      [q|(def id (λ x x))
         (def f (elim-+ id g))
         (def g (λ x (f (Left x))))
         (f (Right 3))|]
        `returns` vFloat 3

    it "if~" $ do
      "(if~ 3 $v (+ v 1) 0)" `returns` vFloat 4
      "(if~ 3 3 1 0)" `returns` vFloat 1
      "(if~ 3 2 1 0)" `returns` vFloat 0

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Nothing Nothing 1 0)
        |] `returns` vFloat 1

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) Nothing 1 0)
        |] `returns` vFloat 0

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Nothing (Just $x) x 0)
        |] `returns` vFloat 0

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) (Just $x) x 0)
        |] `returns` vFloat 3

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) (Just 3) 1 0)
        |] `returns` vFloat 1

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) (Just 2) 1 0)
        |] `returns` vFloat 0

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just Nil) (Just Nil) 1 0)
        |] `returns` vFloat 1

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just (Cons 3 Nil)) (Just Nil) 1 0)
        |] `returns` vFloat 0

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just Nil) (Just (Cons $hd $tl)) (, hd tl) (, 0 Nil))
        |] `returns` Tag "," [vFloat 0, Tag "Nil" []]

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just (Cons 3 Nil)) (Just (Cons $hd $tl)) (, hd tl) (, 0 Nil))
        |] `returns` Tag "," [vFloat 3, Tag "Nil" []]

      [q|(if~ (, 3 "foo") (, $a $b) (, b a) (error! "impossible"))
        |] `returns` Tag "," [vString "foo", vFloat 3]

    it "error!" $ do
      [q|(error! "foo")|] `failsWith` "foo"
      [q|(if~ 0 0 1 (error! "foo"))|] `returns` vFloat 1
      [q|(if~ 0 1 1 (error! "foo"))|] `failsWith` "foo"

  describe "Type declaration" $ do
    let failsWith :: String -> String -> Expectation
        failsWith prog err = case runEval prog of
          Left x -> Text.unpack x `shouldStartWith` err
          Right _ -> expectationFailure "Expected Left"

    let returns :: String -> Val -> Expectation
        prog `returns` v = runEval prog `shouldBe` Right v

    it "simple type declaration" $ do
      [q|(type Foo Bar Baz) (if~ 0 0 Bar Baz)|]
        `returns` Tag "Bar" []

      [q|(type Maybe-Float Nothing (Just Float)) (if~ 3 0 Nothing (Just 3))|]
        `returns` Tag "Just" [vFloat 3]

      [q|(type Point (Point Float Float Float)) (Point 1 2 3)|]
        `returns` Tag "Point" [vFloat 1, vFloat 2, vFloat 3]

    it "(mutually) recursive type declarations" $ do
      [q|(type List-Float FNil (FCons Float List-Float)) (FCons 3 FNil)|]
        `returns` Tag "FCons" [vFloat 3, Tag "FNil" []]

      [q|(type Foo (Foo Bar)) (type Bar X (Bar Foo)) (Bar (Foo (Bar (Foo X))))|]
        `returns` Tag "Bar" [Tag "Foo" [Tag "Bar" [Tag "Foo" [Tag "X" []]]]]

    it "forbids name conflicts in type declarations" $ do
      [q|(type A A) (type A A) 1|] `failsWith` "CEMultiDeclareType"

    it "forbids name conflicts in constructors" $ do
      [q|(type A A) (type B A) 1|]
        `failsWith` "CEMultiDeclareConstructor"

    it "allows type variables" $ do
      [q|(type (Maybe $a) Nothing (Just $a)) Nothing|]
        `returns` Tag "Nothing" []

      [q|(type (Maybe $a) Nothing (Just $a)) (Just 3)|]
        `returns` Tag "Just" [vFloat 3]

      [q|(type (L $a) L (C $a (L $a))) (C 3 L)|]
        `returns` Tag "C" [vFloat 3, Tag "L" []]

      [q|(type (L $a) L (C $a (L $a))) (C 4 (C 3 L))|]
        `returns` Tag "C" [vFloat 4, Tag "C" [vFloat 3, Tag "L" []]]

    it "allows constructors to not use all type variables" $ do
      [q|(type (E $l $r) (L $l) (R $r)) (, (L 3) (R "foo"))|]
        `returns` Tag "," [Tag "L" [vFloat 3], Tag "R" [vString "foo"]]

    it "forbids novel type variables in constructors" $ do
      [q|(type (Maybe $x) (Just $y)) (Just 3)|]
        `failsWith` "CEUnknownType"

    it "type eliminators" $ do
      [q|(type Foo Bar) (elim-Foo 3 Bar)|] `returns` vFloat 3
      [q|(type Foo (Bar Float)) (elim-Foo (λ x x) (Bar 3))|] `returns` vFloat 3
      [q|(type (Foo $x) (Bar $x)) (elim-Foo (λ x x) (Bar 3))
        |] `returns` vFloat 3
      [q|(type (Foo $x) (Bar $x String))
         (elim-Foo (λ (x y) (, x y)) (Bar 3 "Blah"))
        |] `returns` Tag "," [vFloat 3, vString "Blah"]

      [q|(type Foo Bar Baz) (elim-Foo 3 4 Bar)|] `returns` vFloat 3
      [q|(type Foo Bar Baz) (elim-Foo 3 4 Baz)|] `returns` vFloat 4
      [q|(type (Maybe $a) Nothing (Just $a))
         (, (elim-Maybe (, 1 "blah") (, 2) Nothing)
            (elim-Maybe (, 1 "blah") (, 2) (Just "boop")))
        |] `returns` Tag "," [ Tag "," [vFloat 1, vString "blah"]
                             , Tag "," [vFloat 2, vString "boop"] ]
      [q|(def sum (elim-List 0
                             (λ (n l) (+ n (sum l)))))
         (, (sum Nil)
            (, (sum (Cons 3 Nil))
               (sum (Cons 3 (Cons 5 Nil)))))
        |] `returns` Tag "," [vFloat 0, Tag "," [vFloat 3, vFloat 8]]

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
