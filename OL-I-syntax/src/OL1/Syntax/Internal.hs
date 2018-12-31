module OL1.Syntax.Internal (prettyShow) where

import qualified Text.PrettyPrint.ANSI.Leijen as A

prettyShow :: A.Pretty a => a -> String
prettyShow x = A.displayS (stripSGR $ A.renderSmart 0.4 80 $ A.pretty x) ""

stripSGR :: A.SimpleDoc -> A.SimpleDoc
stripSGR A.SFail         = A.SFail
stripSGR A.SEmpty        = A.SEmpty
stripSGR (A.SChar x d)   = A.SChar x (stripSGR d)
stripSGR (A.SText i x d) = A.SText i x (stripSGR d)
stripSGR (A.SLine i d)   = A.SLine i (stripSGR d)
stripSGR (A.SSGR _ d)    = stripSGR d
