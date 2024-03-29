module Prelude.Extra
  ( module Prelude.Extra
  , module Export
  )
where

import Control.Applicative as Export ((<|>))
import Control.Lens as Export ((^.), (.~), (%~), (&))
import Control.Monad as Export ((<=<), (>=>), foldM, forM, forM_, void, when)
import Control.Monad.Extra as Export (whenJust)
import Control.Monad.Trans as Export (MonadIO(..))
import Data.Bifunctor as Export (first, second)
import Data.Either as Export (isLeft)
import Data.Either.Extra as Export (mapLeft)
import Data.List as Export (foldl', group, sort)
import Data.List.NonEmpty as Export (NonEmpty(..))
import Data.Generics.Product as Export (field, getField, setField)
import Data.Map.Strict as Export (Map)
import Data.Maybe as Export (catMaybes, mapMaybe)
import Data.Set as Export (Set)
import Data.Text as Export (Text)
import Data.Void as Export (Void, absurd)
import qualified Data.Text as Text
import GHC.Generics as Export (Generic)
import GHC.Stack as Export (HasCallStack)

tshow :: Show a => a -> Text
tshow = Text.pack . show
