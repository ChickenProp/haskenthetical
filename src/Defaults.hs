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

defaultSymbols :: Env
defaultSymbols = Env $ Map.fromList
  [ ("+", Builtin $ Builtin' "+" hplus)
  , (",", Builtin $ Builtin' "," hcons)
  , ("car", Builtin $ Builtin' "car" hcar)
  , ("cdr", Builtin $ Builtin' "cdr" hcdr)
  , ("Left", Builtin $ Builtin' "Left" (Right . HLeft))
  , ("Right", Builtin $ Builtin' "Right" (Right . HRight))
  , ("either", Builtin $ Builtin' "either" heither)
  ]

-- TODO: unify this with defaultSymbols
defaultTypes :: TypeEnv
defaultTypes = TypeEnv $ Map.fromList
  [ ("+", Forall [] (tFloat :-> tFloat :-> tFloat))
  , ("three", Forall [] tFloat)
  , (",", Forall [a', b'] $ a :-> b :-> (a ::* b))
  , ("car", Forall [a', b'] $ (a ::* b) :-> a)
  , ("cdr", Forall [a', b'] $ (a ::* b) :-> b)
  , ("Left", Forall [a', b'] $ a :-> (a ::+ b))
  , ("Right", Forall [a', b'] $ b :-> (a ::+ b))
  , ("either", Forall [a', b', c']
      $ (a :-> c) :-> (b :-> c) :-> (a ::+ b) :-> c)
  ]
  where a' = TV "a"
        a = TVar a'
        b' = TV "b"
        b = TVar b'
        c' = TV "c"
        c = TVar c'