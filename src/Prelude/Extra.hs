module Prelude.Extra
  ( module Prelude.Extra
  , module Control.Lens
  , module Control.Monad
  , module Control.Monad.Trans
  , module Data.Bifunctor
  , module Data.Either
  , module Data.Generics.Product
  , module Data.Maybe
  , Generic
  , Map
  , Text
  )
where

import Control.Lens ((^.), (.~), (%~), (&))
import Control.Monad (foldM, forM, void, when)
import Control.Monad.Trans (liftIO)
import Data.Bifunctor (first, second)
import Data.Either (isLeft)
import Data.Generics.Product (field, getField, setField)
import Data.Map (Map)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Generics (Generic)

tshow :: Show a => a -> Text
tshow = Text.pack . show
