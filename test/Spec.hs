
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
   stmts <- first tshow $ treesToStmts trees

   let decls = flip mapMaybe stmts $ \case
         TypeDecl d -> Just d
         _ -> Nothing
   newEnv <- first tshow $ declareTypes decls defaultEnv

   expr1 <- def2let stmts
   first tshow $ runTypeCheck (getInferEnv newEnv) expr1

runEval :: String -> Either Text Val
runEval program = do
   trees <- first tshow $ parseWholeFile "<str>" program
   stmts <- first tshow $ treesToStmts trees

   let decls = flip mapMaybe stmts $ \case
         TypeDecl d -> Just d
         _ -> Nothing
   newEnv <- first tshow $ declareTypes decls defaultEnv

   expr1 <- def2let stmts
   void $ first tshow $ runTypeCheck (getInferEnv newEnv) expr1
   eval1 (getSymbols newEnv) (rmType expr1)

main :: IO ()
main = hspec $ do
  let vFloat = Literal . Float
      vString = Literal . String

  describe "Type checking" $ do
    let hasType :: String -> PType Tc -> Expectation
        prog `hasType` t = typeCheck prog `shouldBe` Right t

    let tcFails :: String -> Expectation
        tcFails prog = typeCheck prog `shouldSatisfy` isLeft

        tcFailsWith :: String -> String -> Expectation
        tcFailsWith prog err = case typeCheck prog of
          Left x -> Text.unpack x `shouldStartWith` err
          Right _ -> expectationFailure "Expected Left"

    let tvh :: Name -> TVar Tc
        tvh = TV HType

        ttvh :: Name -> MType Tc
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

    it "accepts unused function arguments" $ do
      [q|(def const3 (λ x 3))
         (, (const3 "foo") (const3 4))
        |] `hasType` Forall [] (tFloat +:* tFloat)

      [q|(def const (λ (x y) x))
         (, (const 3 "foo") (const 3 4))
        |] `hasType` Forall [] (tFloat +:* tFloat)

    it "accepts typed constants" $ do
      "(: 3 Float)" `hasType` Forall [] tFloat
      [q|(: "foo" String)|] `hasType` Forall [] tString

    it "accepts typed expressions" $ do
      "(: + (-> Float (-> Float Float)))"
        `hasType` Forall [] (tFloat +-> tFloat +-> tFloat)
      "(: (+ 1) (-> Float Float))" `hasType` Forall [] (tFloat +-> tFloat)
      [q|(: (λ x (if~ x 0 (Left 0) (Right 0)))
            (-> Float (+ Float Float)))
        |] `hasType` Forall [] (tFloat +-> (tFloat +:+ tFloat))
      [q|(: (, 2 "bar") (, Float String))|]
        `hasType` Forall [] (tFloat +:* tString)

    it "accepts types in patterns" $ do
      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Nothing (: Nothing (Maybe Float)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Nothing (: Nothing (Maybe String)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) (: Nothing (Maybe Float)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just "foo") (: Nothing (Maybe Float)) 3 1)
        |] `tcFailsWith` "CEUnificationFail"

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Nothing (: (Just $x) (Maybe Float)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Nothing (Just (: $x Float)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) (Just (: $x Float)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just 3) (Just (: 3 Float)) 3 1)
        |] `hasType` Forall [] tFloat

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just "foo") (Just (: $x Float)) 3 1)
        |] `tcFailsWith` "CEUnificationFail"

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just "foo") (Just (: 3 Float)) 3 1)
        |] `tcFailsWith` "CEUnificationFail"

      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ (Just "foo") (Just (: "foo" Float)) 3 1)
        |] `tcFailsWith` "CEUnificationFail"

    it "rejects incorrectly typed constants" $ do
      "(: 3 String)" `tcFailsWith` "CEUnificationFail"
      [q|(: "foo" Float)|] `tcFailsWith` "CEUnificationFail"
      "(: 3 (, Float))" `tcFailsWith` "CEKindMismatch"

    it "rejects incorrectly typed pattern bindings" $ do
      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ 3 Nothing 1 0)
        |] `tcFailsWith` "CEUnificationFail"

    it "rejects incorrectly typed lambda args" $ do
      "(λ ((: a String)) (+ a 1))" `tcFailsWith` "CEUnificationFail"

    it "rejects pattern matching on incomplete constructors" $ do
      pendingWith "Not yet implemented."
      [q|(type (Maybe $a) Nothing (Just $a))
         (if~ Just Just 1 0)
        |] `tcFailsWith` "Something"

    it "rejects pattern matching on non-constructors" $ do
      pendingWith "Not yet implemented."
      [q|(type (Maybe $a) Nothing (Just $a))
         (def my-nothing Nothing)
         (if~ Nothing my-nothing 1 0)
        |] `tcFailsWith` "Something"

    it "Allows declaring types as not their most general possibility" $ do
      [q|(def (: id-Float (-> Float Float)) (λ x x))
         (id-Float "blah")
        |] `tcFailsWith` "CEUnificationFail"

      [q|(def id-Float (: (λ x x) (-> Float Float)))
         (id-Float "blah")
        |] `tcFailsWith` "CEUnificationFail"

      [q|(let ((id (λ x x))
               ((: id-Float (-> Float Float)) id))
           (, (id "blah") (, (id 3) (id-Float 3))))
        |] `hasType` Forall [] (tString +:* (tFloat +:* tFloat))

      [q|(let ((id (λ x x))
               (id-Float (: id (-> Float Float))))
           (, (id "blah") (, (id 3) (id-Float 3))))
        |] `hasType` Forall [] (tString +:* (tFloat +:* tFloat))

      [q|(let (((: id-Float (-> Float Float)) (λ x x)))
           (id-Float "blah"))
        |] `tcFailsWith` "CEUnificationFail"

      [q|(let ((id-Float (: (λ x x) (-> Float Float))))
           (id-Float "blah"))
        |] `tcFailsWith` "CEUnificationFail"

    it "Type declarations with variables" $ do
      [q|(def (: id (-> $a $a)) (λ x x))
         (id "blah")
        |] `hasType` Forall [] tString

      [q|(let (((: id (-> $a $a)) (λ x x)))
           (id "blah"))
        |] `hasType` Forall [] tString

      [q|(let (((: id (-> String $a)) (λ x x)))
           (id "blah"))
        |] `tcFailsWith` "CEDeclarationTooGeneral"

      [q|(let (((: id (-> $a String)) (λ x x)))
           (id "blah"))
        |] `tcFailsWith` "CEDeclarationTooGeneral"

      [q|(def (: id (-> String $a)) (λ x x))
         (id "blah")
        |] `tcFailsWith` "CEDeclarationTooGeneral"

      [q|(def (: id (-> $a String)) (λ x x))
         (id "blah")
        |] `tcFailsWith` "CEDeclarationTooGeneral"

      [q|(def id (λ x x))
         ((: id (-> $a $a)) "foo")
        |] `hasType` Forall [] tString

      [q|(def id (λ x x))
         ((: id (-> String $a)) "foo")
        |] `tcFailsWith` "CEDeclarationTooGeneral"

      [q|(def id (λ x x))
         ((: id (-> $a String)) "foo")
        |] `tcFailsWith` "CEDeclarationTooGeneral"

      [q|(def id (λ x x))
         (: (id "blah") $a)
        |] `tcFailsWith` "CEDeclarationTooGeneral"

    it "Calculates minimally recursive binding groups" $ do
      -- This is necessary because, when typechecking `(letrec ((n a)) e)`, `n`
      -- is only available as a monotype when evaluating `a`. Or as "Typing
      -- Haskell in Haskell" puts it, we need to
      --
      -- > ensure that each variable is used with the same type at every
      -- > occurrence within the defining list of bindings. (Lifting this
      -- > restriction makes type inference undecidable (Henglein, 1993; Kfoury
      -- > et al., 1993).)
      --
      -- http://web.cecs.pdx.edu/~mpj/thih/thih.pdf (p. 33)
      --
      -- We can demonstrate the need for this in Haskell as well, by introducing
      -- a mutual dependency into the group:
      --
      -- (1)    let a1 x = x
      --            a2 = (a1 :: Float -> Float) }
      --        in a1 ""
      -- (2)    let a1 x = const x (a2 3)
      --            a2 = (a1 :: Float -> Float)
      --        in a1 ""
      -- (3)    let a1 :: a -> a
      --            a1 x = const x (a2 3)
      --            a2 = (a1 :: Float -> Float)
      --        in a1 ""
      -- (4)    let a1 x = const x (a2 3)
      --            a2 :: Float -> Float
      --            a2 = a1
      --        in a1 ""
      --
      -- (1) typechecks, because we calculate the type of `a1` without looking
      -- at `a2`. But (2) doesn't, because we can't do that. Thus, a1 is given
      -- the monotype `Float -> Float` which doesn't generalize very far. (3)
      -- and (4) typecheck because bindings with explicit type declarations can
      -- be placed in a separate dependency group.
      --
      -- (Not sure I'm going to implement this any time soon.)
      pendingWith "Not yet implemented"

      [q|(def id (λ x x))
         (def (: (-> Float Float) id-Float) id)
         (, (id "blah") (, (id 3) (id-Float 3)))
        |] `hasType` Forall [] (tString +:* (tFloat +:* tFloat))

      [q|(def id (λ x x))
         (def id-Float (: (-> Float Float) id))
         (, (id "blah") (, (id 3) (id-Float 3)))
        |] `hasType` Forall [] (tString +:* (tFloat +:* tFloat))


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
                  (f (either id g))
                  (g (λ x (f (Left x)))))
             (f (Right 3)))|]
        `returns` vFloat 3
      [q|(def id (λ x x))
         (def f (either id g))
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
         (type (List $a) Nil (Cons $a (List $a)))
         (if~ (Just Nil) (Just Nil) 1 0)
        |] `returns` vFloat 1

      [q|(type (Maybe $a) Nothing (Just $a))
         (type (List $a) Nil (Cons $a (List $a)))
         (if~ (Just (Cons 3 Nil)) (Just Nil) 1 0)
        |] `returns` vFloat 0

      [q|(type (Maybe $a) Nothing (Just $a))
         (type (List $a) Nil (Cons $a (List $a)))
         (if~ (Just Nil) (Just (Cons $hd $tl)) (, hd tl) (, 0 Nil))
        |] `returns` Tag "," [vFloat 0, Tag "Nil" []]

      [q|(type (Maybe $a) Nothing (Just $a))
         (type (List $a) Nil (Cons $a (List $a)))
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
      [q|(type List-Float Nil (Cons Float List-Float)) (Cons 3 Nil)|]
        `returns` Tag "Cons" [vFloat 3, Tag "Nil" []]

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

      [q|(type (List $a) Nil (Cons $a (List $a))) (Cons 3 Nil)|]
        `returns` Tag "Cons" [vFloat 3, Tag "Nil" []]

      [q|(type (List $a) Nil (Cons $a (List $a))) (Cons 4 (Cons 3 Nil))|]
        `returns` Tag "Cons" [vFloat 4, Tag "Cons" [vFloat 3, Tag "Nil" []]]

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
      [q|(type (List $a) Nil (Cons $a (List $a)))
         (def sum (elim-List 0
                             (λ (n l) (+ n (sum l)))))
         (, (sum Nil)
            (, (sum (Cons 3 Nil))
               (sum (Cons 3 (Cons 5 Nil)))))
        |] `returns` Tag "," [vFloat 0, Tag "," [vFloat 3, vFloat 8]]
