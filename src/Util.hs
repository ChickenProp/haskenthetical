module Util
  ( module Util
  , Text
  , liftIO
  , when
  )
where

import Control.Monad (when)
import Control.Monad.Trans (liftIO)
import Data.Text (Text)
import qualified Data.Text as Text

tshow :: Show a => a -> Text
tshow = Text.pack . show
