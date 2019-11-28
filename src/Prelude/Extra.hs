module Prelude.Extra
  ( module Prelude.Extra
  , module Control.Lens
  , module Control.Monad
  , module Control.Monad.Trans
  , module Data.Either
  , module Data.Generics.Product
  , Generic
  , Map
  , Text
  )
where

import Control.Lens ((^.), (.~), (%~), (&))
import Control.Monad (forM, void, when)
import Control.Monad.Trans (liftIO)
import Data.Either (isLeft)
import Data.Generics.Product (field, getField, setField)
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Generics (Generic)

tshow :: Show a => a -> Text
tshow = Text.pack . show
