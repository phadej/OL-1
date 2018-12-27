{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Writer (Writer, execWriter, tell)
import Data.Bifunctor       (first)
import Data.List            (sort)
import System.Directory     (listDirectory)
import System.FilePath      (takeExtension, (-<.>), (</>))
import Test.Tasty           (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden    (goldenVsStringDiff)

import qualified Data.ByteString            as BS
import qualified Data.ByteString.Lazy       as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import qualified Data.ByteString.UTF8       as UTF8

import OL1 hiding ((</>))

import OL1.Syntax.FromSyntax (fromSyntax, runParser)
import OL1.Syntax.Parser     (parseSyntax)
import OL1.Syntax.Pretty     (syntaxToString)
import OL1.Syntax.Sugar      (desugar)
import OL1.Syntax.Sym        (Sym)
-- import OL1.Syntax.ToSyntax   (runPrinter, toSyntax)

main :: IO ()
main = do
    dirContents <- listDirectory "fixtures"
    let cases = map mkCase $ sort $ filter (\fp -> takeExtension fp == ".ol1") dirContents
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
        expr0 <- either throwError pure $ runParser (fromSyntax s1) :: M (Chk Sym Sym)
        tellString $ pretty expr0

        header "INFERED"
        (expr1, _ws) <- either (throwError . pretty) pure $ synth
            ctx
            (Ann (first Just expr0) (Mono $ T Nothing))
        tellString $ pretty expr1

        header "CHECKED"
        (_val, ty) <- either (throwError . pretty) pure $ infer
            ctx
            expr1
        tellString $ pretty ty

        header "EVALED"
        -- tellString $ syntaxToString $ runPrinter $ toSyntax val

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

    ctx :: Sym -> Maybe (Poly Sym)
    ctx "f" = Just $ Mono ("A" :-> "B")
    ctx "x" = Just $ Mono "A"

    ctx _ = Nothing

type M = ExceptT String (Writer [BS.ByteString])
