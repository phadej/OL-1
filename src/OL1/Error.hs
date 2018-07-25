{-# LANGUAGE OverloadedStrings #-}
module OL1.Error where

import Control.Exception        (Exception)
import Data.String              (IsString (..))
import Text.PrettyPrint.Compact (($$), (<+>), (</>))

import qualified Control.Unification      as U
import qualified Text.PrettyPrint.Compact as PP

import OL1.Pretty

-- | Various errors occuring during type-checking of terms.
data Err
    = SomeErr String
      -- ^ /untyped/ error. Avoid.
    | VariableNotInScope Doc [Doc]
      -- ^ variable not in the context provided
    | TypeMismatch Doc Doc Doc [Doc]
      -- ^ type mismatch in function application
    | LambdaNotArrow Doc Doc [Doc]
      -- ^ Lambda is (annotated with) not an arrow type
    | PolyNotForall Doc Doc [Doc]
      -- ^ type abstraction is (annotated with) not a polymorphic type
    | NotAFunction Doc Doc Doc [Doc]
      -- ^ apply warning in 'Term' type-checker.
    | NotAPolyFunction Doc Doc Doc [Doc]
      -- ^ type apply warning in 'Term' type-checker.
    | ApplyPanic Doc
      -- ^ apply panic in 'Value' evaluator
    | OccursFailure Doc Doc
      -- ^ Occurs failure, i.e infinite type
    | MismatchFailure Doc Doc

instance Show Err where
    -- TODO: use renderWith
    showsPrec _ e = showString $ PP.render (ppr e)

instance Exception Err

instance (Pretty1 t, Pretty v) => U.Fallible t v Err where
    occursFailure v t = OccursFailure (ppr v) (ppr1 t)
    mismatchFailure a b = MismatchFailure (ppr1 a) (ppr1 b)

instance IsString Err where
    fromString = SomeErr

instance Pretty Err where
    ppr (SomeErr err) = "error:" </> PP.string err
    ppr (VariableNotInScope x ctx) = ppCheckedTerms ctx $
        "error:" </> err
      where
        err = "Variable not in scope" <+> x
    ppr (TypeMismatch expt act term ctx) = ppCheckedTerms ctx $
        "error:" </> types $$ term'
      where
        types = "Couldn't match expected type" <+> expt <+> "with actual type" <+> act
        term' = "In the expression:" <+> term
    ppr (LambdaNotArrow t term ctx) = ppCheckedTerms ctx $
        "error:" </> err $$ ann
      where
        err = "The lambda expression" <+> term <+> "doesn't have an arrow type"
        ann = "Annotated with" <+> t
    ppr (PolyNotForall t term ctx) = ppCheckedTerms ctx $
        "error:" </> err $$ ann
      where
        err = "The type abstraction" <+> term <+> "doesn't have a polymorphic type"
        ann = "Annotated with" <+> t
    ppr (NotAFunction t f x ctx) = ppCheckedTerms ctx $
        "error:" </> err $$ f' $$ x'
      where
        err = "Couldn't match actual type" <+> t <+> "with a function type"
        f' = "In the application of" <+> f
        x' = "to the value" <+> x
    ppr (NotAPolyFunction t f x ctx) = ppCheckedTerms ctx $
        "error:" </> err $$ f' $$ x'
      where
        err = "Couldn't match actual type" <+> t <+> "with a type abstraction"
        f' = "In the type application of" <+> f
        x' = "to the type" <+> x

    ppr (ApplyPanic f) =
        PP.text "panic:" </> err
      where
        err = "Trying to apply not-a-lambda" <+> f

    ppr (OccursFailure v t) =
        "error:" </>
        "Occurs check, cannot construct infinite type" <+> v <+> " ~ " <+> t
    ppr (MismatchFailure a b) =
        "error:" </>
        "Couldn't match expected type" <+> b <+> "with actual type" <+> a

ppCheckedTerms :: [Doc] -> Doc -> Doc
ppCheckedTerms [] doc = doc
ppCheckedTerms ts doc = doc
    $$ "when checking expressions"
    $$ PP.vcat ts
