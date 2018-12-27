{-# LANGUAGE RecordWildCards #-}
module Main (main) where

main :: IO ()
main = return ()

{-
import OL1 hiding ((</>))

import Data.Bifunctor    (first)
import Data.Text         (Text)
import System.FilePath   ((-<.>), (</>))
import Test.Tasty        (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsString)

import qualified Data.ByteString.Lazy.UTF8 as UTF8
import qualified Data.Map.Strict           as Map

idType_ :: Poly Text
idType_ = forall_ "a" $ "a" :-> "a"

idTerm_ :: Chk Text Text
idTerm_ = poly_ "a" $ lam_ "x" "x"

id_ :: Inf (Maybe Text) Text
id_ = Ann (first Just idTerm_) (fmap Just idType_)

main :: IO ()
main = defaultMain $ testGroup "Golden"
    [ golden "id" $ defCase
        { term = Ann (lam_ "x" "x") wildcard
        }
    , golden "id-poly" $ defCase
        { term = id_
        }
    , golden "id-poly-infer" $ defCase
        { term = Ann (first Just idTerm_) $ Nothing <$ forall_ "a" ("a" :-> "_")
        }
    , golden "id-id" $ defCase
        { term = "id" $$ "id"
        , ctx  = [ "id" ~> idType_ ]
        }
    , golden "id-id-2" $ defCase
        { term = id_ $$ "id"
        , ctx  = [ "id" ~> idType_ ]
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
    , golden "rigid" $ defCase
        { term = first Just $
            Ann (poly_ "x" "f") (forall_ "a" $ "a" :-> "a")
        }
    , golden "rigid2" $ defCase
        { term = first Just $
            Ann (poly_ "x" "f") (forall_ "a" $ "a" :-> "a")
        , ctx =
            [ "f" ~> Mono $ "A" :-> "A"
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
    $ pretty
    $ ppr term
    $$$ ppr ctx
    $$$ ppr resPpr
    $$$ mempty
  where
    res     = synth ctx'' term
    ctx'    = Map.fromList ctx
    ctx'' n = Map.lookup n ctx'

    resPpr = do
        (synTerm, ws) <- res
        if null ws
        then do
            ty <- infer ctx'' synTerm
            return $ ppr (synTerm, ty, ws)
        else return $ ppr (synTerm, ws)

wildcard :: Poly (Maybe a)
wildcard = Mono $ T Nothing
-}
