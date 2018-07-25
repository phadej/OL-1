{-# LANGUAGE RecordWildCards #-}
module Main (main) where

import OL1

import System.FilePath   ((-<.>), (</>))
import Test.Tasty        (defaultMain, testGroup, TestTree)
import Test.Tasty.Golden (goldenVsString)

import qualified Data.ByteString.Lazy.UTF8 as UTF8
import qualified Text.PrettyPrint.Compact   as PP
import qualified Data.Map.Strict as Map

main :: IO ()
main = defaultMain $ testGroup "Golden"
    [ golden "id" $ defCase
        { term = Ann (lam_ "x" "x") wildcard
        }
    , golden "id-id" $ defCase
        { term = "id" $$ "id"
        , ctx  = [ "id" ~> forall_ "a" $ "a" :-> "a" ]
        }
    , golden "f-x-y" $ defCase
        { term = "f" $$ "x" $$ "y"
        }
    , golden "occurs" $ defCase
        { term = "x" $$ "x"
        }
    , golden "type-error" $ defCase
        { term = "f" $$ "x"
        , ctx = 
            [ "f" ~> Mono $ "A" :-> "B"
            , "x" ~> Mono "C"
            ]
        }
    ]

-------------------------------------------------------------------------------
-- Test utiliteis
-------------------------------------------------------------------------------

data Case = Case
    { term :: Inf (Maybe Text) Text
    , ctx  :: [(Text, Poly Text)]
    }

defCase :: Case
defCase = Case
    { term = "x"
    , ctx  = []
    }

infixr 0 ~>
(~>) :: Text -> Poly Text -> (Text, Poly Text)
(~>) = (,)

golden :: String -> Case -> TestTree
golden name Case {..} = goldenVsString name ("golden" </> name -<.> "txt")
    $ return $ UTF8.fromString
    $ PP.render
    $ ppr term
    PP.$$ ppr ctx
    PP.$$ ppr res
    PP.$$ mempty
  where
    res     = synth ctx'' term
    ctx'    = Map.fromList ctx
    ctx'' n = Map.lookup n ctx'

wildcard :: Poly (Maybe a)
wildcard = Mono $ T Nothing
