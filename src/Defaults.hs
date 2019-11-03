module Defaults (defaultTypes, defaultSymbols) where

import Prelude.Extra
import qualified Data.Map as Map

import Eval
import Syntax
import TypeCheck

rbb :: Name -> (Val -> Either Text Val) -> Either Text Val
rbb name func = Right $ Builtin $ Builtin' name func

hplus :: Val -> Either Text Val
hplus (Float a) = rbb "+.1" $ \case
  Float b -> Right $ Float (a + b)
  _ -> Left "+ only accepts floats"
hplus _ = Left "+ only accepts floats"

hminus :: Val -> Either Text Val
hminus (Float a) = rbb "-.1" $ \case
  Float b -> Right $ Float (a - b)
  _ -> Left "- only accepts floats"
hminus _ = Left "- only accepts floats"

htimes :: Val -> Either Text Val
htimes (Float a) = rbb "*.1" $ \case
  Float b -> Right $ Float (a * b)
  _ -> Left "* only accepts floats"
htimes _ = Left "* only accepts floats"

hcons :: Val -> Either Text Val
hcons v1 = rbb "cons.1" $ \v2 -> Right $ v1 :* v2

hcar :: Val -> Either Text Val
hcar (a :* _) = Right a
hcar _ = Left "car only accepts pairs"

hcdr :: Val -> Either Text Val
hcdr (_ :* b) = Right b
hcdr _ = Left "cdr only accepts pairs"

heither :: Val -> Either Text Val
heither l = rbb "either.1" $ \r -> rbb "either.2" $ \case
  HLeft v -> call l v
  HRight v -> call r v
  _ -> Left "final argument of either must be an Either"

hif0 :: Val -> Either Text Val
hif0 (Float v) = rbb "if0.1" $ \then_ -> rbb "if0.2" $ \else_ ->
  if v == 0 then Right then_ else Right else_
hif0 _ = Left "first arg to if0 must be a Float"

defaults :: Map Name (Val, PType Tc)
defaults = Map.fromList
  [ "+" ~~ bb "+" hplus ~~ Forall [] (tFloat +-> tFloat +-> tFloat)
  , "-" ~~ bb "-" hminus ~~ Forall [] (tFloat +-> tFloat +-> tFloat)
  , "*" ~~ bb "*" htimes ~~ Forall [] (tFloat +-> tFloat +-> tFloat)
  , "," ~~ bb "," hcons ~~ Forall [a', b'] (a +-> b +-> (a +:* b))
  , "car" ~~ bb "car" hcar ~~ Forall [a', b'] ((a +:* b) +-> a)
  , "cdr" ~~ bb "cdr" hcdr ~~ Forall [a', b'] ((a +:* b) +-> b)
  , "Left" ~~ bb "Left" (Right . HLeft) ~~ Forall [a', b'] (a +-> (a +:+ b))
  , "Right" ~~ bb "Right" (Right . HRight) ~~ Forall [a', b'] (b +-> (a +:+ b))
  , "either"
      ~~ bb "either" heither
      ~~ Forall [a', b', c'] ((a +-> c) +-> (b +-> c) +-> (a +:+ b) +-> c)
  , "if0" ~~ bb "if0" hif0  ~~ Forall [a'] (tFloat +-> a +-> a +-> a)
  ]
  where a' = TV "a"
        a = TVar a'
        b' = TV "b"
        b = TVar b'
        c' = TV "c"
        c = TVar c'

        bb n f = Builtin (Builtin' n f)
        infixr 1 ~~
        (~~) = (,)

defaultSymbols :: Env
defaultSymbols = Env $ fst <$> defaults

defaultTypes :: TypeEnv
defaultTypes = TypeEnv $ snd <$> defaults
