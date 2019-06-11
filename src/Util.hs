module Util
  ( module Util
  , Text
  )
where

import Data.Text (Text)
import qualified Data.Text as Text

tshow :: Show a => a -> Text
tshow = Text.pack . show
