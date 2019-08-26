
import Prelude.Extra

import Test.Hspec
import Text.InterpolatedString.Perl6 (q)

import Defaults
import Eval
import Parser
import Syntax
import TypeCheck


typeCheck :: String -> Either Text PType
typeCheck program = do
   trees <- parseWholeFile "<str>" program
   exprs <- treesToExprs trees
   expr1 <- def2let exprs
   runTypeCheck defaultTypes expr1

runEval :: String -> Either Text Val
runEval program = do
   trees <- parseWholeFile "<str>" program
   exprs <- treesToExprs trees
   expr1 <- def2let exprs
   void $ runTypeCheck defaultTypes expr1
   eval1 defaultSymbols expr1

main :: IO ()
main = hspec $ do
  describe "Type checking" $ do
    let hasType :: String -> PType -> Expectation
        prog `hasType` t = typeCheck prog `shouldBe` Right t

    let tcFails :: String -> Expectation
        tcFails prog = typeCheck prog `shouldSatisfy` isLeft

    it "accepts constants" $ do
      "3" `hasType` Forall [] tFloat
      [q|"foo"|] `hasType` Forall [] tString

    it "accepts lambdas" $ do
      "(λ x x)" `hasType` Forall [TV "a"] (TVar (TV "a") :-> TVar (TV "a"))

    it "applies functions" $ do
      "(+ 1)" `hasType` Forall [] (tFloat :-> tFloat)
      "(+ 1 2)" `hasType` Forall [] tFloat

    it "rejects poly typed lambda args" $ do
      tcFails [q|(λ f (, (f 3) (f "")))|]

    it "accepts poly typed let args" $ do
      [q|(let ((f (λ x (, x x)))) (, (f 3) (f "")))|]
        `hasType` Forall [] ((tFloat ::* tFloat) ::* (tString ::* tString))

  describe "Evaluation" $ do
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
        `returns`  Float 3
