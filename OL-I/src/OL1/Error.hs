{-# LANGUAGE OverloadedStrings #-}
module OL1.Error where

import Control.Exception         (Exception)
import Control.Unification.Rigid
       (Fallible (..), RigidFallible (..), RigidFallibleAll (..),
       RigidVariable, Variable)
import Data.String               (IsString (..))
import Text.PrettyPrint.Compact ((<+>), ($$), (</>))

import qualified Text.PrettyPrint.Compact as PP

import OL1.Syntax

-- | Various errors occuring during type-checking of terms.
data Err
    = SomeErr String
      -- ^ /untyped/ error. Avoid.
    | VariableNotInScope SyntaxI [SyntaxI]
      -- ^ variable not in the context provided
    | TypeMismatch SyntaxI SyntaxI SyntaxI [SyntaxI]
      -- ^ type mismatch in function application
    | LambdaNotArrow SyntaxI SyntaxI [SyntaxI]
      -- ^ Lambda is (annotated with) not an arrow type
    | PolyNotForall SyntaxI SyntaxI [SyntaxI]
      -- ^ type abstraction is (annotated with) not a polymorphic type
    | PairNotProd SyntaxI SyntaxI [SyntaxI]
      -- ^ Pair is annotated with not a product type
    | NotAFunction SyntaxI SyntaxI SyntaxI [SyntaxI]
      -- ^ apply warning in 'Term' type-checker.
    | NotAPolyFunction SyntaxI SyntaxI SyntaxI [SyntaxI]
      -- ^ type apply warning in 'Term' type-checker.
    | NotATuple SyntaxI SyntaxI [SyntaxI]
      -- ^ fst/snd  warning in 'Term' type-checker.
    | ApplyPanic SyntaxI
      -- ^ apply panic in 'Value' evaluator
    | OccursFailure SyntaxI SyntaxI
      -- ^ Occurs failure, i.e infinite type
    | MismatchFailure SyntaxI SyntaxI
      -- ^ ...
    | RigidMismatchFailure SyntaxI SyntaxI
      -- ^ ...
    | EscapingRigidFailure SyntaxI
      -- ^ Skolem or rigid meta-variable escaping the scope
    | RigidBindFailure SyntaxI SyntaxI
      -- ^ Skolem or rigid meta-variable escaping the scope

instance Show Err where
    -- TODO: use renderWith
    showsPrec _ e = showString $ PP.render $ prettyErr e

instance Exception Err

instance IsString Err where
    fromString = SomeErr

instance (Variable v, ToSyntax1 t, ToSyntax v) => Fallible t v Err where
    occursFailure v t   = OccursFailure (toSyntax' v) (toSyntax1' t)
    mismatchFailure a b = MismatchFailure (toSyntax1' a) (toSyntax1' b)

instance (ToSyntax n) => RigidFallible n Err where
    rigidMismatchFailure a b = RigidMismatchFailure (toSyntax' a) (toSyntax' b)
    escapingRigidFailure a = EscapingRigidFailure (toSyntax' a)

instance (RigidVariable n v, ToSyntax n, ToSyntax1 t, ToSyntax v) => RigidFallibleAll n t v Err where
    rigidBindFailure n t = RigidBindFailure (toSyntax' n) (toSyntax1' t)

prettyErr :: Err -> PP.Doc ()
prettyErr (SomeErr err) = "error:" </> PP.text err

prettyErr (VariableNotInScope x ctx) = ppCheckedTerms ctx $
    "error:" </> err
  where
    err = "Variable not in scope" <+> prettySyntax x
prettyErr (TypeMismatch expt act term ctx) = ppCheckedTerms ctx $
    "error:" </> types $$ term'
  where
    types = "Couldn't match expected type" <+> prettySyntax expt <+> "with actual type" <+> prettySyntax act
    term' = "In the expression:" <+> prettySyntax term
prettyErr (LambdaNotArrow t term ctx) = ppCheckedTerms ctx $
    "error:" </> err $$ ann
  where
    err = "The lambda expression" <+> prettySyntax term <+> "doesn't have an arrow type"
    ann = "Annotated with" <+> prettySyntax t
prettyErr (PairNotProd t term ctx) = ppCheckedTerms ctx $
    "error:" </> err $$ ann
  where
    err = "The tuple expression" <+> prettySyntax term <+> "doesn't have a tuple type"
    ann = "Annotated with" <+> prettySyntax t
prettyErr (PolyNotForall t term ctx) = ppCheckedTerms ctx $
    "error:" </> err $$ ann
  where
    err = "The type abstraction" <+> prettySyntax term <+> "doesn't have a polymorphic type"
    ann = "Annotated with" <+> prettySyntax t
prettyErr (NotAFunction t f x ctx) = ppCheckedTerms ctx $
    "error:" </> err $$ f' $$ x'
  where
    err = "Couldn't match actual type" <+> prettySyntax t <+> "with a function type"
    f' = "In the application of" <+> prettySyntax f
    x' = "to the value" <+> prettySyntax x
prettyErr (NotAPolyFunction t f x ctx) = ppCheckedTerms ctx $
    "error:" </> err $$ f' $$ x'
  where
    err = "Couldn't match actual type" <+> prettySyntax t <+> "with a type abstraction"
    f' = "In the type application of" <+> prettySyntax f
    x' = "to the type" <+> prettySyntax x
prettyErr (NotATuple t x ctx) = ppCheckedTerms ctx $
    "error:" </> err $$ f' $$ x'
  where
    err = "Couldn't match actual type" <+> prettySyntax t <+> "with a tuple type"
    f' = "In the type application of fst or snd"
    x' = "to the value" <+> prettySyntax x
prettyErr (ApplyPanic f) =
    "panic:" </> err
  where
    err = "Trying to apply not-a-lambda" <+> prettySyntax f

prettyErr (OccursFailure v t) =
    "error:" </>
    "Occurs check, cannot construct infinite type" <+> prettySyntax v <+> " ~ " <+> prettySyntax t
prettyErr (MismatchFailure a b) =
    "error:" </>
    "Couldn't match expected type" <+> prettySyntax b <+> "with actual type" <+> prettySyntax a
prettyErr (EscapingRigidFailure a) =
    "error:" </>
    "Rigid variable" <+> prettySyntax a <+> "escaping its scope"
prettyErr (RigidMismatchFailure a b) =
    "error:" </>
    "Couldn't match rigid type" <+> prettySyntax b <+> "with actual rigid type" <+> prettySyntax a
prettyErr (RigidBindFailure a b) =
    "error:" </>
    "Couldn't match type" <+> prettySyntax b <+> "with actual rigid type" <+> prettySyntax a

ppCheckedTerms :: [SyntaxI] -> PP.Doc () -> PP.Doc ()
ppCheckedTerms [] doc = doc
ppCheckedTerms ts doc = doc
    $$ "when checking expressions"
    $$ PP.vcat (map prettySyntax ts)
