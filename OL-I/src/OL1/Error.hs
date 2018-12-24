{-# LANGUAGE OverloadedStrings #-}
module OL1.Error where

import Control.Exception         (Exception)
import Control.Unification.Rigid
       (Fallible (..), RigidFallible (..), RigidFallibleAll (..),
       RigidVariable, Variable)
import Data.String               (IsString (..))

import qualified Text.PrettyPrint.Compact as PP

import OL1.Pretty

-- | Various errors occuring during type-checking of terms.
data Err
    = SomeErr String
      -- ^ /untyped/ error. Avoid.
    | VariableNotInScope MDoc [MDoc]
      -- ^ variable not in the context provided
    | TypeMismatch MDoc MDoc MDoc [MDoc]
      -- ^ type mismatch in function application
    | LambdaNotArrow MDoc MDoc [MDoc]
      -- ^ Lambda is (annotated with) not an arrow type
    | PolyNotForall MDoc MDoc [MDoc]
      -- ^ type abstraction is (annotated with) not a polymorphic type
    | NotAFunction MDoc MDoc MDoc [MDoc]
      -- ^ apply warning in 'Term' type-checker.
    | NotAPolyFunction MDoc MDoc MDoc [MDoc]
      -- ^ type apply warning in 'Term' type-checker.
    | ApplyPanic MDoc
      -- ^ apply panic in 'Value' evaluator
    | OccursFailure MDoc MDoc
      -- ^ Occurs failure, i.e infinite type
    | MismatchFailure MDoc MDoc
      -- ^ ...
    | RigidMismatchFailure MDoc MDoc
      -- ^ ...
    | EscapingRigidFailure MDoc
      -- ^ Skolem or rigid meta-variable escaping the scope
    | RigidBindFailure MDoc MDoc
      -- ^ Skolem or rigid meta-variable escaping the scope

instance Show Err where
    -- TODO: use renderWith
    showsPrec _ e = showString $ pretty (ppr e)

instance Exception Err

instance IsString Err where
    fromString = SomeErr

instance (Variable v, Pretty1 t, Pretty v) => Fallible t v Err where
    occursFailure v t   = OccursFailure (ppr v) (ppr1 t)
    mismatchFailure a b = MismatchFailure (ppr1 a) (ppr1 b)

instance (Pretty n) => RigidFallible n Err where
    rigidMismatchFailure a b = RigidMismatchFailure (ppr a) (ppr b)
    escapingRigidFailure a = EscapingRigidFailure (ppr a)

instance (RigidVariable n v, Pretty n, Pretty1 t, Pretty v) => RigidFallibleAll n t v Err where
    rigidBindFailure n t = RigidBindFailure (ppr n) (ppr1 t)

instance Pretty Err where
    ppr (SomeErr err) = "error:" </> pprText err
    ppr (VariableNotInScope x ctx) = ppCheckedTerms ctx $
        "error:" </> err
      where
        err = "Variable not in scope" <+> x
    ppr (TypeMismatch expt act term ctx) = ppCheckedTerms ctx $
        "error:" </> types $$$ term'
      where
        types = "Couldn't match expected type" <+> expt <+> "with actual type" <+> act
        term' = "In the expression:" <+> term
    ppr (LambdaNotArrow t term ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ ann
      where
        err = "The lambda expression" <+> term <+> "doesn't have an arrow type"
        ann = "Annotated with" <+> t
    ppr (PolyNotForall t term ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ ann
      where
        err = "The type abstraction" <+> term <+> "doesn't have a polymorphic type"
        ann = "Annotated with" <+> t
    ppr (NotAFunction t f x ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ f' $$$ x'
      where
        err = "Couldn't match actual type" <+> t <+> "with a function type"
        f' = "In the application of" <+> f
        x' = "to the value" <+> x
    ppr (NotAPolyFunction t f x ctx) = ppCheckedTerms ctx $
        "error:" </> err $$$ f' $$$ x'
      where
        err = "Couldn't match actual type" <+> t <+> "with a type abstraction"
        f' = "In the type application of" <+> f
        x' = "to the type" <+> x

    ppr (ApplyPanic f) =
        "panic:" </> err
      where
        err = "Trying to apply not-a-lambda" <+> f

    ppr (OccursFailure v t) =
        "error:" </>
        "Occurs check, cannot construct infinite type" <+> v <+> " ~ " <+> t
    ppr (MismatchFailure a b) =
        "error:" </>
        "Couldn't match expected type" <+> b <+> "with actual type" <+> a
    ppr (EscapingRigidFailure a) =
        "error:" </>
        "Rigid variable" <+> a <+> "escaping its scope"
    ppr (RigidMismatchFailure a b) =
        "error:" </>
        "Couldn't match rigid type" <+> b <+> "with actual rigid type" <+> a
    ppr (RigidBindFailure a b) =
        "error:" </>
        "Couldn't match type" <+> b <+> "with actual rigid type" <+> a

ppCheckedTerms :: [MDoc] -> MDoc -> MDoc
ppCheckedTerms [] doc = doc
ppCheckedTerms ts doc = doc
    $$$ "when checking expressions"
    $$$ (PP.vcat <$> sequenceA ts)
