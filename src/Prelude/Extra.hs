module Prelude.Extra
  ( module Prelude.Extra
  , Text
  , Map
  , forM
  , liftIO
  , when
  )
where

import Control.Monad (forM, when)
import Control.Monad.Trans (liftIO)
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as Text

tshow :: Show a => a -> Text
tshow = Text.pack . show
