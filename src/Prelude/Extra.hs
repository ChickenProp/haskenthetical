module Prelude.Extra
  ( module Prelude.Extra
  , Text
  , Map
  , isLeft
  , forM
  , liftIO
  , void
  , when
  )
where

import Control.Monad (forM, void, when)
import Control.Monad.Trans (liftIO)
import Data.Either (isLeft)
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as Text

tshow :: Show a => a -> Text
tshow = Text.pack . show
