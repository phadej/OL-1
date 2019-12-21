module OL1.Syntax.Internal (prettyShow) where

import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.String as PP

prettyShow :: PP.Doc a -> String
prettyShow x = PP.renderString (PP.layoutPretty layoutOptions (PP.unAnnotate x))
  where
    layoutOptions = PP.LayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine 80 1 }

