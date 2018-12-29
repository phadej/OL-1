{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Lens
import Control.Monad.Except       (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict
import Control.Monad.Writer       (Writer, execWriter, tell)
import Data.Foldable              (for_)
import Data.List                  (sort)
import System.Directory           (listDirectory)
import System.FilePath            (takeExtension, (-<.>), (</>))
import Test.Tasty                 (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden          (goldenVsStringDiff)

import qualified Data.ByteString            as BS
import qualified Data.ByteString.Lazy       as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import qualified Data.ByteString.UTF8       as UTF8
import qualified Data.Map.Strict            as Map

import OL1
import OL1.Syntax

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

    return $ LBS8.unlines $ map LBS.fromStrict $ execWriter $ runE $ flip evalStateT emptyS $ do
        header "INPUT"
        tell [ contents ]

        ss <- either throwError pure $ parseSyntaxes input contents

        ifor_ ss $ \i s0 -> do
            header $ "PARSED " ++ show (i + 1)
            tellString $ syntaxToString s0

            case s0 of
                SList ["postulate", SSym n, s1] -> do
                    header "POSTULATE"
                    ty <- either throwError pure $ runParser (fromSyntax s1) :: M (Poly Sym)
                    tellString $ pretty n ++ " := " ++ pretty ty

                    postulated . at n ?= ty

                SList ["define", SSym n, s1] -> do
                    header "DEFINE"
                    (expr, ty, _val) <- inference s1

                    defined %= ((n, expr, ty) :)

                _ -> do
                    header "EVALUATE"
                    (expr, _ty, _val) <- inference s0
    

                    header "EXPANDED"

                    post <- use postulated
                    let ctx :: Sym -> Maybe (Poly Sym)
                        ctx n = post ^? ix n

                    defs <- use defined
                    let subst :: (Sym, Inf Sym Sym, Poly Sym) -> Inf Sym Sym -> Inf Sym Sym
                        subst (n, x, _) t = t >>= \n' -> if n' == n then x else return n'
                    let expr1 = foldr subst expr defs

                    tellString $ pretty expr1

                    header "EVALUATED VALUE"
                    (val, _ty) <- either (throwError . show) pure $ infer
                        ctx
                        expr1
                    tellString $ pretty val
  where
    input  = "fixtures" </> name -<.> "ol1"
    output = "fixtures" </> name -<.> "out"

    tellString :: String -> M ()
    tellString s = tell [ UTF8.fromString s, BS.empty ]

    runE :: M' () -> Writer [BS.ByteString] ()
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

    inference :: Syntax -> M (Inf Sym Sym, Poly Sym, Intro Sym Sym)
    inference s0 = do
        -- no header
        expr0 <- either throwError pure $ runParser (fromSyntax s0) :: M (Chk (Maybe Sym) Sym)
        tellString $ pretty expr0

        header "INFERRED"
        post <- use postulated
        defs <- use defined
        let defs' = Map.union post $ Map.fromList [ (n, t) | (n, _, t) <- defs ]
        let ctx :: Sym -> Maybe (Poly Sym)
            ctx n = defs' ^? ix n

        (expr2, ws) <- either (throwError . show) pure $ synth
            ctx
            (ann_ expr0 $ Mono $ T Nothing)

        for_ ws $ \(NotInScope s ty) -> tellString $
            "WARN: " ++ pretty (sthe (toSyntax ty) (toSyntax s))

        tellString $ pretty expr2

        header "CHECKED TYPE"
        (val, ty) <- either (throwError . show) pure $ infer
            ctx
            expr2
        tellString $ pretty ty

        return (expr2, ty, val)

ann_ :: Chk b a -> Poly b -> Inf b a
ann_ (Inf a) _ = a
ann_ a       b = Ann a b

pretty :: ToSyntax a => a -> String
pretty = syntaxToString . runPrinter . toSyntax

type M  = StateT S M'
type M' = ExceptT String (Writer [BS.ByteString])

data S = S
    { _postulated :: Map.Map Sym (Poly Sym)
    , _defined    :: [(Sym, Inf Sym Sym, Poly Sym)] -- ^ reversed order!
    }

postulated :: Lens' S (Map.Map Sym (Poly Sym))
postulated f s = f (_postulated s) <&> \x -> s { _postulated = x }

defined :: Lens' S [(Sym, Inf Sym Sym, Poly Sym)]
defined f s = f (_defined s) <&> \x -> s { _defined = x }

emptyS :: S
emptyS = S
    { _postulated = Map.empty
    , _defined    = []
    }
