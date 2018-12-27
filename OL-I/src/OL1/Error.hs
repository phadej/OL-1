{-# LANGUAGE OverloadedStrings #-}
module OL1.Error where

import Control.Exception         (Exception)
import Control.Unification.Rigid
       (Fallible (..), RigidFallible (..), RigidFallibleAll (..),
       RigidVariable, Variable)
import Data.String               (IsString (..))

import qualified Text.PrettyPrint.Compact as PP

import OL1.Pretty
import OL1.Syntax

-- | Various errors occuring during type-checking of terms.
data Err
    = SomeErr String
      -- ^ /untyped/ error. Avoid.
    | VariableNotInScope Syntax [Syntax]
      -- ^ variable not in the context provided
    | TypeMismatch Syntax Syntax Syntax [Syntax]
      -- ^ type mismatch in function application
    | LambdaNotArrow Syntax Syntax [Syntax]
      -- ^ Lambda is (annotated with) not an arrow type
    | PolyNotForall Syntax Syntax [Syntax]
      -- ^ type abstraction is (annotated with) not a polymorphic type
    | NotAFunction Syntax Syntax Syntax [Syntax]
      -- ^ apply warning in 'Term' type-checker.
    | NotAPolyFunction Syntax Syntax Syntax [Syntax]
      -- ^ type apply warning in 'Term' type-checker.
    | ApplyPanic Syntax
      -- ^ apply panic in 'Value' evaluator
    | OccursFailure Syntax Syntax
      -- ^ Occurs failure, i.e infinite type
    | MismatchFailure Syntax Syntax
      -- ^ ...
    | RigidMismatchFailure Syntax Syntax
      -- ^ ...
    | EscapingRigidFailure Syntax
      -- ^ Skolem or rigid meta-variable escaping the scope
    | RigidBindFailure Syntax Syntax
      -- ^ Skolem or rigid meta-variable escaping the scope

instance Show Err where
    -- TODO: use renderWith
    showsPrec _ e = showString $ pretty (ppr e)

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

instance Pretty Err where
    ppr (SomeErr err) = "error:" </> pprText err
    ppr (VariableNotInScope x ctx) = ppCheckedTerms ctx $
        "error:" </> err
      where
        err = "Variable not in scope" <+> ppr x
    ppr (TypeMismatch expt act term ctx) = ppCheckedTerms ctx $
        "error:" </> types $$$ term'
      where
        types = "Couldn't match expected type" <+> ppr expt <+> "with actual type" <+> ppr act
        term' = "In the expression:" <+> ppr term
    ppr (LambdaNotArrow t term ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ ann
      where
        err = "The lambda expression" <+> ppr term <+> "doesn't have an arrow type"
        ann = "Annotated with" <+> ppr t
    ppr (PolyNotForall t term ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ ann
      where
        err = "The type abstraction" <+> ppr term <+> "doesn't have a polymorphic type"
        ann = "Annotated with" <+> ppr t
    ppr (NotAFunction t f x ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ f' $$$ x'
      where
        err = "Couldn't match actual type" <+> ppr t <+> "with a function type"
        f' = "In the application of" <+> ppr f
        x' = "to the value" <+> ppr x
    ppr (NotAPolyFunction t f x ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ f' $$$ x'
      where
        err = "Couldn't match actual type" <+> ppr t <+> "with a type abstraction"
        f' = "In the type application of" <+> ppr f
        x' = "to the type" <+> ppr x

    ppr (ApplyPanic f) =
        "panic:" </> err
      where
        err = "Trying to apply not-a-lambda" <+> ppr f

    ppr (OccursFailure v t) =
        "error:" </>
        "Occurs check, cannot construct infinite type" <+> ppr v <+> " ~ " <+> ppr t
    ppr (MismatchFailure a b) =
        "error:" </>
        "Couldn't match expected type" <+> ppr b <+> "with actual type" <+> ppr a
    ppr (EscapingRigidFailure a) =
        "error:" </>
        "Rigid variable" <+> ppr a <+> "escaping its scope"
    ppr (RigidMismatchFailure a b) =
        "error:" </>
        "Couldn't match rigid type" <+> ppr b <+> "with actual rigid type" <+> ppr a
    ppr (RigidBindFailure a b) =
        "error:" </>
        "Couldn't match type" <+> ppr b <+> "with actual rigid type" <+> ppr a

ppCheckedTerms :: [Syntax] -> MDoc -> MDoc
ppCheckedTerms [] doc = doc
ppCheckedTerms ts doc = doc
    $$$ "when checking expressions"
    $$$ (PP.vcat <$> traverse ppr ts)
