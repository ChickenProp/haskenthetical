module Defaults (defaultEnv) where

import Prelude.Extra
import qualified Data.Map.Strict as Map

import Env
import Eval
import Syntax

rbb :: Name -> (Val -> Either Text Val) -> Either Text Val
rbb name func = Right $ Builtin $ Builtin' name func

hplus :: Val -> Either Text Val
hplus (Literal (Float a)) = rbb "+.1" $ \case
  Literal (Float b) -> Right $ Literal $ Float (a + b)
  _ -> Left "+ only accepts floats"
hplus _ = Left "+ only accepts floats"

hminus :: Val -> Either Text Val
hminus (Literal (Float a)) = rbb "-.1" $ \case
  Literal (Float b) -> Right $ Literal $ Float (a - b)
  _ -> Left "- only accepts floats"
hminus _ = Left "- only accepts floats"

htimes :: Val -> Either Text Val
htimes (Literal (Float a)) = rbb "*.1" $ \case
  Literal (Float b) -> Right $ Literal $ Float (a * b)
  _ -> Left "* only accepts floats"
htimes _ = Left "* only accepts floats"

hcons :: Val -> Either Text Val
hcons v1 = rbb "cons.1" $ \v2 -> Right $ Tag "," [v1, v2]

hcar :: Val -> Either Text Val
hcar (Tag "," [a, _]) = Right a
hcar _ = Left "car only accepts pairs"

hcdr :: Val -> Either Text Val
hcdr (Tag "," [_, b]) = Right b
hcdr _ = Left "cdr only accepts pairs"

heither :: Val
heither = mkBuiltinUnsafe $ do
  l <- getArg "either"
  r <- getArg "either.1"
  e <- getArg "either.2"
  pure $ case e of
    Tag "Left" [v] -> call l v
    Tag "Right" [v] -> call r v
    _ -> Left "final argument of either must be an Either"

hif0 :: Val -> Either Text Val
hif0 (Literal (Float v)) = mkBuiltin $ do
  then_ <- getArg "if0.1"
  else_ <- getArg "if0.2"
  pure $ Right $ if v == 0 then then_ else else_
hif0 _ = Left "first arg to if0 must be a Float"

defaultVarEnv :: Map Name (PType Tc, Val)
defaultVarEnv = fmap (\(x, y) -> (y, x)) $ Map.fromList
  [ "+" ~~ bb "+" hplus ~~ Forall [] (tFloat +-> tFloat +-> tFloat)
  , "-" ~~ bb "-" hminus ~~ Forall [] (tFloat +-> tFloat +-> tFloat)
  , "*" ~~ bb "*" htimes ~~ Forall [] (tFloat +-> tFloat +-> tFloat)
  , "," ~~ bb "," hcons ~~ Forall [a', b'] (a +-> b +-> (a +:* b))
  , "car" ~~ bb "car" hcar ~~ Forall [a', b'] ((a +:* b) +-> a)
  , "cdr" ~~ bb "cdr" hcdr ~~ Forall [a', b'] ((a +:* b) +-> b)
  , "Left"
      ~~ bb "Left" (Right . Tag "Left" . (: []))
      ~~ Forall [a', b'] (a +-> (a +:+ b))
  , "Right"
      ~~ bb "Right" (Right . Tag "Right" . (: []))
      ~~ Forall [a', b'] (b +-> (a +:+ b))
  , "either"
      ~~ heither
      ~~ Forall [a', b', c'] ((a +-> c) +-> (b +-> c) +-> (a +:+ b) +-> c)
  , "if0" ~~ bb "if0" hif0  ~~ Forall [a'] (tFloat +-> a +-> a +-> a)
  ]
  where a' = TV HType "a"
        a = TVar a'
        b' = TV HType "b"
        b = TVar b'
        c' = TV HType "c"
        c = TVar c'

        bb n f = Builtin (Builtin' n f)
        infixr 1 ~~
        (~~) = (,)

defaultTypeEnv :: TypeEnv MType
defaultTypeEnv = Map.fromList
  [ ("Float", tFloat)
  , ("String", tString)
  , ("->", TCon $ TC (HType :*-> HType :*-> HType) "->")
  , ("+", TCon $ TC (HType :*-> HType :*-> HType) "+")
  , (",", TCon $ TC (HType :*-> HType :*-> HType) ",")
  ]

defaultEnv :: FullEnv
defaultEnv = FullEnv { feVars = defaultVarEnv, feTypes = defaultTypeEnv }
