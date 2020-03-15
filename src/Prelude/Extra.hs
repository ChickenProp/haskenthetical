module Prelude.Extra
  ( module Prelude.Extra
  , module Export
  )
where

import Control.Lens as Export ((^.), (.~), (%~), (&))
import Control.Monad as Export ((<=<), (>=>), foldM, forM, void, when)
import Control.Monad.Trans as Export (liftIO)
import Data.Bifunctor as Export (first, second)
import Data.Either as Export (isLeft)
import Data.List as Export (foldl')
import Data.Generics.Product as Export (field, getField, setField)
import Data.Map.Strict as Export (Map)
import Data.Maybe as Export (mapMaybe)
import Data.Text as Export (Text)
import qualified Data.Text as Text
import GHC.Generics as Export (Generic)

tshow :: Show a => a -> Text
tshow = Text.pack . show
