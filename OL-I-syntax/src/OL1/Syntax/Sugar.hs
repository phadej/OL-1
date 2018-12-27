module OL1.Syntax.Sugar (
    desugar,
    ) where

import OL1.Syntax.Type

desugar :: Syntax -> Syntax
desugar = id
