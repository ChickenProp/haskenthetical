module Gist
  ( Gist(..)
  , prettyGist
  ) where

import Prelude.Extra

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.TreeDiff
import Text.PrettyPrint (Doc)

class Gist a where
  gist :: a -> Expr
  default gist :: ToExpr a => a -> Expr
  gist = toExpr

prettyGist :: Gist a => a -> Doc
prettyGist = prettyExpr . gist

instance Gist Double
instance Gist Text

instance (Gist a, Gist b) => Gist (a, b) where
  gist (a, b) = toExpr (gist a, gist b)

instance Gist a => Gist [a] where
  gist = Lst . map gist

instance (Gist k, Gist v) => Gist (Map k v) where
  gist m = App "Map" $ gist <$> Map.toList m

instance Gist a => Gist (Set a) where
  gist s = App "Set" $ gist <$> Set.toList s
