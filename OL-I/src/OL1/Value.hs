{-# LANGUAGE OverloadedStrings #-}
module OL1.Value where

import Prelude ()
import Prelude.Compat

import Bound.Class          (Bound (..))
import Bound.Scope.Simple
       (Scope, hoistScope, instantiate1)
import Bound.ScopeH         (ScopeH, fromScopeH, instantiate1H, toScopeH)
import Bound.Var            (Var (..))
import Control.Monad        (ap, void)
import Control.Monad.Module (Module (..))
import Data.Bifoldable      (Bifoldable (..))
import Data.Bifunctor       (Bifunctor (..))
import Data.Bitraversable   (Bitraversable (..), bifoldMapDefault, bimapDefault)
import Data.Coerce          (coerce)
import Data.Functor.Classes (Eq1 (..), eq1)
import Data.String          (IsString (..))

import qualified Data.Text       as T
import qualified Data.Text.Short as TS

import OL1.Error
import OL1.Name
import OL1.Pretty
import OL1.Type

import OL1.Syntax
import OL1.Syntax.Sym
import OL1.Syntax.ToSyntax

-- | 'Intro' has a normal deduction, \(A\!\uparrow\).
data Intro b a
    = VLam N (Scope N (Intro b) a)
    | VLamTy N (ScopeH N (Intro' a) Mono b)
    | VCoerce (Elim b a)
    | VErr Err

newtype Intro' a b = Intro' { unIntro' :: Intro b a }

overIntro' :: (Intro b a -> Intro d c) -> Intro' a b -> Intro' c d
overIntro' = coerce

-- | 'Elim' is extracted from a hypothesis, \(A\!\downarrow\).
data Elim b a
    = VApp (Elim b a) (Intro b a)
    | VAppTy (Elim b a) (Mono b)
    | VVar a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Functor (Intro b) where
    fmap = second

instance Functor (Intro' a) where
    fmap = second

instance Functor (Elim b) where
    fmap = second

instance Pretty b => Applicative (Intro b) where
    pure = VCoerce . pure
    (<*>) = ap

instance Pretty b => Monad (Intro b) where
    return = pure

    (>>=) :: forall a c. Intro b a -> (a -> Intro b c) -> Intro b c
    VLam n b         >>= k = VLam n (b >>>= k)
    VCoerce u        >>= k = valueAppBind u k
    VErr err         >>= _ = VErr err
    VLamTy n b       >>= k = undefined n b k

{- VLamTy n $ (overScopeH . overIntro') (>>= k') b where
        k' :: a -> Intro (Var N (Mono b)) c
        k' = first (return . return) . k
-}

valueAppBind :: Pretty b => Elim b a -> (a -> Intro b c) -> Intro b c
valueAppBind (VVar a) k     = k a
valueAppBind (VApp f x) k   = valueApp (valueAppBind f k) (x >>= k)
valueAppBind (VAppTy f t) k = valueAppTy (valueAppBind f k) t

instance Pretty b => Applicative (Elim b) where
    pure = VVar
    (<*>) = ap

instance Pretty b => Monad (Elim b) where
    return = pure

    VVar x     >>= k = k x
    VApp f x   >>= k = VApp (f >>= k) (valueBind x k)
    VAppTy x t >>= k = VAppTy (x >>= k) t

valueBind :: Pretty b => Intro b a -> (a -> Elim b c) -> Intro b c
valueBind (VCoerce e)  k = VCoerce (e >>= k)
valueBind (VLam n b)   k = VLam n (b >>>= VCoerce . k)
valueBind (VErr err)   _ = VErr err
valueBind (VLamTy n b) k = VLamTy n $ toScopeH
    $ Intro'
    $ flip valueBind (first F . k)
    $ unIntro'
    $ fromScopeH b

instance Module (Intro' a) Mono where
    Intro' i >>== k = Intro' (bindIntroMono i k)

bindIntroMono :: Intro b a -> (b -> Mono c) -> Intro c a
bindIntroMono (VErr err)   _ = VErr err
bindIntroMono (VCoerce c)  k = VCoerce (bindElimMono c k)
bindIntroMono (VLam n b)   k = VLam n $ hoistScope (`bindIntroMono` k) b
bindIntroMono (VLamTy n b) k = VLamTy n $ b >>== k
 
bindElimMono :: Elim b a -> (b -> Mono c) -> Elim c a
bindElimMono (VVar x)     _ = VVar x
bindElimMono (VApp f x)   k = VApp (bindElimMono f k) (bindIntroMono x k)
bindElimMono (VAppTy x t) k = VAppTy (bindElimMono x k) (t >>= k)

-------------------------------------------------------------------------------
-- Bi*
-------------------------------------------------------------------------------

instance Bifunctor  Elim   where bimap = bimapDefault
instance Bifunctor  Intro  where bimap = bimapDefault
instance Bifunctor  Intro' where bimap = bimapDefault
instance Bifoldable Elim   where bifoldMap = bifoldMapDefault
instance Bifoldable Intro  where bifoldMap = bifoldMapDefault
instance Bifoldable Intro' where bifoldMap = bifoldMapDefault

instance Bitraversable Intro' where
    bitraverse f g = fmap Intro' . bitraverse g f . unIntro'

instance Bitraversable Intro where

instance Bitraversable Elim where

-------------------------------------------------------------------------------
-- V application
-------------------------------------------------------------------------------

-- | Apply to values.
--
-- Note that '@@' from "Language.PTSmart" module is different
valueApp
    :: Pretty b
    => Intro b a  -- ^ f : a -> b
    -> Intro b a  -- ^ x : a
    -> Intro b a  -- ^ _ : b
valueApp (VCoerce f) x = VCoerce (VApp f x)
valueApp (VErr err)  _ = VErr err
valueApp (VLam _ b)  x = instantiate1 x b
valueApp f           _ = VErr (ApplyPanic (ppr (void f)))

valueAppTy
    :: Pretty b
    => Intro b a
    -> Mono b
    -> Intro b a
valueAppTy (VCoerce x)  t = VCoerce (VAppTy x t)
valueAppTy (VErr err)   _ = VErr err
valueAppTy (VLamTy _ b) t = unIntro' $ instantiate1H t b
valueAppTy f            _ = VErr (ApplyPanic (ppr (void f)))

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

instance Eq b => Eq1 (Intro b) where
    liftEq eq (VCoerce x)  (VCoerce x')  = liftEq eq x x'
    liftEq eq (VLam _ x)   (VLam _  x')  = liftEq eq x x'
    liftEq eq (VLamTy _ b) (VLamTy _ b') = liftEq eq
        (unIntro' $ fromScopeH b)
        (unIntro' $ fromScopeH b')

    -- Errors are inequal
    liftEq _  (VErr _) (VErr _) = False

    -- catch all case: False
    liftEq _eq VCoerce {} _ = False
    liftEq _eq VLam    {} _ = False
    liftEq _eq VLamTy  {} _ = False
    liftEq _eq VErr    {} _ = False

instance Eq b => Eq1 (Elim b) where
    liftEq eq (VVar a)     (VVar a')      = eq a a'
    liftEq eq (VApp f x)   (VApp f' x')   = liftEq eq f f' && liftEq eq x x'
    liftEq eq (VAppTy x t) (VAppTy x' t') = liftEq eq x x' && t == t'

    -- False cases
    liftEq _ VVar   {} _ = False
    liftEq _ VApp   {} _ = False
    liftEq _ VAppTy {} _ = False

instance (Eq a, Eq b) => Eq (Intro b a) where (==) = eq1
instance (Eq a, Eq b) => Eq (Elim b a) where (==) = eq1

-------------------------------------------------------------------------------
-- Pretty instances
-------------------------------------------------------------------------------

instance Pretty b => Pretty1 (Intro b) where
    liftPpr pp i = bitraverse ppr pp i >>= pprIntro

instance Pretty b => Pretty1 (Elim b) where
    liftPpr pp x = bitraverse ppr pp x >>= pprElim

instance (Pretty a, Pretty b) => Pretty (Intro b a) where ppr = ppr1
instance (Pretty a, Pretty b) => Pretty (Elim b a)  where ppr = ppr1

pprIntro :: Intro Doc Doc -> MDoc
pprIntro (VErr err)      = ppr err
pprIntro (VLam n b)      = pprScopedC n $ \n' ->
    sexpr (pprText "fn") [ return n', pprIntro $ instantiate1 (return n') b ]
pprIntro (VLamTy n b)    = pprScopedC n $ \n' ->
    sexpr (pprText "poly") [ return n', pprIntro $ unIntro' $ instantiate1H (return n') b ]
pprIntro (VCoerce x)     = pprElim x

pprElim :: Elim Doc Doc -> MDoc
pprElim (VVar a)     = ppr a
pprElim (VApp f x)   = sexpr (pprElim f) [pprIntro x]
pprElim (VAppTy x t) = sexpr (pprElim x) [pprChar '@' <> pprMono t]

-------------------------------------------------------------------------------
-- ToSyntax
-------------------------------------------------------------------------------

instance (a ~ Sym, b ~ Sym) => ToSyntax (Intro a b) where
    toSyntax = toSyntax'

toSyntax' :: Intro Sym Sym -> SyntaxM
toSyntax' (VErr _err) = error "some error!"
toSyntax' (VCoerce x) = toSyntax x
toSyntax' (VLam n b)  = freshen (nToSym n) $ \s ->
    srlist RFn
        [ toSyntax $ instantiate1 (return s) b
        ]
toSyntax' (VLamTy n b)  = freshen (nToSym n) $ \s ->
    srlist' RFn
        [ At <$> toSyntax s
        , At <$> toSyntax s
         , fmap At $ toSyntax $ unIntro' $ instantiate1H (return (Sym "foo")) b
        ]

instance (a ~ Sym, b ~ Sym) => ToSyntax (Elim a b) where
    toSyntax (VVar v)   = ssym v
    toSyntax (VApp f x) = slist (toSyntax f) [toSyntax x]
    toSyntax (VAppTy x t) = slist' (toSyntax x) [At <$> toSyntax t]

nToSym :: N -> Sym
nToSym (N s) = Sym (TS.pack (T.unpack s))

-------------------------------------------------------------------------------
-- Smart
-------------------------------------------------------------------------------

instance IsString a => IsString (Intro b a) where
    fromString = VCoerce . fromString

instance IsString a => IsString (Elim b a) where
    fromString = VVar . fromString
