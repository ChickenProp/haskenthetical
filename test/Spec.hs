
import Prelude.Extra

import qualified Data.Text as Text
import Test.Hspec
import Text.InterpolatedString.Perl6 (q)

import Defaults
import Env
import Eval
import Parser
import Syntax
import TypeCheck


typeCheck :: String -> Either Text (PType Tc)
typeCheck program = do
   trees <- first tshow $ parseWholeFile "<str>" program
   exprs <- first tshow $ treesToExprs trees

   let decls = flip mapMaybe (rmType <$> exprs) $ \case
         TypeDecl d -> Just d
         _ -> Nothing
   newEnv <- first tshow $ declareTypes decls defaultEnv

   expr1 <- def2let exprs
   first tshow $ runTypeCheck (getInferEnv newEnv) expr1

runEval :: String -> Either Text Val
runEval program = do
   trees <- first tshow $ parseWholeFile "<str>" program
   exprs <- first tshow $ treesToExprs trees

   let decls = flip mapMaybe (rmType <$> exprs) $ \case
         TypeDecl d -> Just d
         _ -> Nothing
   newEnv <- first tshow $ declareTypes decls defaultEnv

   expr1 <- def2let exprs
   void $ first tshow $ runTypeCheck (getInferEnv newEnv) expr1
   eval1 (getSymbols newEnv) (rmType expr1)

main :: IO ()
main = hspec $ do
  describe "Type checking" $ do
    let hasType :: String -> PType Tc -> Expectation
        prog `hasType` t = typeCheck prog `shouldBe` Right t

    let tcFails :: String -> Expectation
        tcFails prog = typeCheck prog `shouldSatisfy` isLeft

        tcFailsWith :: String -> String -> Expectation
        tcFailsWith prog err = case typeCheck prog of
          Left x -> Text.unpack x `shouldStartWith` err
          Right _ -> expectationFailure "Expected Left"

    let tvh :: Text -> TVar Tc
        tvh = TV HType

        ttvh :: Text -> MType Tc
        ttvh = TVar . tvh

    it "accepts constants" $ do
      "3" `hasType` Forall [] tFloat
      [q|"foo"|] `hasType` Forall [] tString

    it "accepts lambdas" $ do
      "(λ x x)" `hasType` Forall [tvh "a"] (ttvh "a" +-> ttvh "a")

    it "applies functions" $ do
      "(+ 1)" `hasType` Forall [] (tFloat +-> tFloat)
      "(+ 1 2)" `hasType` Forall [] tFloat

    it "rejects poly typed lambda args" $ do
      tcFails [q|(λ f (, (f 3) (f "")))|]

    it "accepts poly typed let args" $ do
      [q|(let ((f (λ x (, x x)))) (, (f 3) (f "")))|]
        `hasType` Forall [] ((tFloat +:* tFloat) +:* (tString +:* tString))

    it "accepts typed constants" $ do
      "(: Float 3)" `hasType` Forall [] tFloat
      [q|(: String "foo")|] `hasType` Forall [] tString

    it "accepts typed expressions" $ do
      "(: (-> Float (-> Float Float)) +)"
        `hasType` Forall [] (tFloat +-> tFloat +-> tFloat)
      "(: (-> Float Float) (+ 1))" `hasType` Forall [] (tFloat +-> tFloat)
      "(: (-> Float (+ Float Float)) (λ x (if0 x (Left 0) (Right 0))))"
        `hasType` Forall [] (tFloat +-> (tFloat +:+ tFloat))
      [q|(: (, Float String) (, 2 "bar"))|]
        `hasType` Forall [] (tFloat +:* tString)

    it "rejects incorrectly typed constants" $ do
      "(: String 3)" `tcFailsWith` "CEUnificationFail"
      [q|(: Float "foo")|] `tcFailsWith` "CEUnificationFail"
      "(: (, Float) 3)" `tcFailsWith` "CEKindMismatch"

  describe "Evaluation" $ do
    let failsWith :: String -> String -> Expectation
        failsWith prog err = case runEval prog of
          Left x -> Text.unpack x `shouldStartWith` err
          Right _ -> expectationFailure "Expected Left"

    let returns :: String -> Val -> Expectation
        prog `returns` v = runEval prog `shouldBe` Right v

    it "evals constants" $ do
      "3" `returns` Float 3
      [q|"foo"|] `returns` String "foo"

    it "performs arithmetic" $ do
      "(+ 3 4)" `returns` Float 7
      "(+ 3 (+ 4 5))" `returns` Float 12
      "(+ (+ 3 4) 5)" `returns` Float 12
      "(+ (+ 3.2 4.1) 5.3)" `returns` Float 12.6
      "(- 3 4)" `returns` Float (-1)
      "(* 7.2 3.1)" `returns` Float 22.32

    it "if0" $ do
      [q|(if0 0 "foo" "bar")|] `returns` String "foo"
      [q|(if0 1 "foo" "bar")|] `returns` String "bar"

    it "factorial" $ do
      -- if0 evaluates both branches, so we use thunks to stop infinite loops
      [q|(letrec ((fac (λ x ((if0 x (λ s 1) (λ s (* x (fac (- x 1))))) 1))))
           (fac 3))|] `returns` Float 6

    it "letrec" $ do
      [q|(letrec ((id (λ x x))
                  (f (either id g))
                  (g (λ x (f (Left x)))))
             (f (Right 3)))|]
        `returns` Float 3

    it "type declaration" $ do
      [q|(type Foo Bar Baz) (if0 0 Bar Baz)|]
        `returns` Tag "Bar" []

      [q|(type Maybe-Float Nothing (Just Float)) (if0 3 Nothing (Just 3))|]
        `returns` Tag "Just" [Float 3]

      [q|(type Point (Point Float Float Float)) (Point 1 2 3)|]
        `returns` Tag "Point" [Float 1, Float 2, Float 3]

    it "(mutually) recursive type declarations" $ do
      [q|(type List-Float Nil (Cons Float List-Float)) (Cons 3 Nil)|]
        `returns` Tag "Cons" [Float 3, Tag "Nil" []]

      [q|(type Foo (Foo Bar)) (type Bar X (Bar Foo)) (Bar (Foo (Bar (Foo X))))|]
        `returns` Tag "Bar" [Tag "Foo" [Tag "Bar" [Tag "Foo" [Tag "X" []]]]]

    it "forbids name conflicts in type declarations" $ do
      [q|(type A A) (type A A) 1|] `failsWith` "CEMultiDeclareType"

    it "forbids name conflicts in constructors" $ do
      [q|(type A A) (type B A) 1|]
        `failsWith` "CEMultiDeclareConstructor"
