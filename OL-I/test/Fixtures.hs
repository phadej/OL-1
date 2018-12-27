module Main (main) where

import OL1 hiding ((</>))

import OL1.Syntax.FromSyntax (runParser, fromSyntax)
import OL1.Syntax.Parser     (parseSyntax)
import OL1.Syntax.Pretty     (syntaxToString)
import OL1.Syntax.Sugar      (desugar)
import OL1.Syntax.Sym        (Sym)

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Writer (Writer, execWriter, tell)
import System.Directory     (listDirectory)
import System.FilePath      (takeExtension, (-<.>), (</>))
import Test.Tasty           (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden    (goldenVsStringDiff)

import qualified Data.ByteString            as BS
import qualified Data.ByteString.Lazy       as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import qualified Data.ByteString.UTF8       as UTF8

main :: IO ()
main = do
    dirContents <- listDirectory "fixtures"
    let cases = fmap mkCase $ filter (\fp -> takeExtension fp == ".ol1") dirContents
    defaultMain $ testGroup "Fixtures" cases

-------------------------------------------------------------------------------
-- Test utilities
-------------------------------------------------------------------------------

mkCase :: FilePath -> TestTree
mkCase name = goldenVsStringDiff name diff output $ do
    contents <- BS.readFile input

    return $ LBS8.unlines $ map LBS.fromStrict $ execWriter $ runE $ do
        header "INPUT"
        tell [ contents ]

        header "PARSED"
        s0 <- either throwError pure $ parseSyntax input contents
        tellString $ syntaxToString s0

        header "DESUGARED"
        let s1 = desugar s0
        tellString $ syntaxToString s1

        header "FROMSYNTAX"
        expr <- either throwError pure $ runParser (fromSyntax s1) :: M (Chk Sym Sym)
        tellString $ pretty expr

  where
    input  = "fixtures" </> name -<.> "ol1"
    output = "fixtures" </> name -<.> "out"

    tellString :: String -> M ()
    tellString s = tell [ UTF8.fromString s, BS.empty ]

    runE :: M () -> Writer [BS.ByteString] ()
    runE m = do
        x <- runExceptT m
        case x of
            Right () -> pure ()
            Left err -> tell
                [ "ERROR"
                , UTF8.fromString err
                ]

    header :: String -> M ()
    header n = tell
        [ UTF8.fromString $ "=== " ++ n ++ " " ++ replicate (72 - length n) '='
        ]

    diff ref new = ["diff", "-u", ref, new]

type M = ExceptT String (Writer [BS.ByteString])
