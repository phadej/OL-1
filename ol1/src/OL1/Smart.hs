module OL1.Smart where

import Data.Text (Text)
import OL1.Type

class SLam u where
    -- | Lambda-abstraction.
    --
    -- >>> prettyPut $ (lam_ "x" "x" :: Inf () Text)
    -- (fn x x)
    --
    lam_ :: Text -> u b Text -> u b Text

    poly_ :: Text -> u Text a -> u Text a
 
class SApp a b c | c -> a b where
    ($$) :: a y x -> b y x -> c y x

class SAppTy a c | c -> a where
    (@@) :: a y x -> Mono y -> c y x

infixl 2 $$, @@

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import OL1
