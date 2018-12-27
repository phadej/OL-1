{-# LANGUAGE OverloadedStrings #-}
module OL1.Value where

import Prelude ()
import Prelude.Compat

import Bound.Class          (Bound (..))
import Bound.Scope.Simple   (Scope (..), toScope, fromScope, hoistScope, instantiate1, bitraverseScope)
import Bound.Var            (Var (..))
import Control.Monad        (ap, void)
import Control.Monad.Module (Module (..))
import Data.Bifoldable      (Bifoldable (..))
import Data.Bifunctor       (Bifunctor (..))
import Data.Bitraversable   (Bitraversable (..), bifoldMapDefault, bimapDefault)
import Data.Coerce          (coerce)
import Data.Functor.Classes
       (Eq1 (..), Show1 (..), Show2 (..), eq1, showsBinaryWith, showsPrec2,
       showsUnaryWith)
import Data.String          (IsString (..))

import OL1.Error
import OL1.Type
import OL1.Syntax
import OL1.Syntax.Sym
import OL1.Syntax.ToSyntax

-- | 'Intro' has a normal deduction, \(A\!\uparrow\).
data Intro b a
    = VLam ISym (Mono b) (Scope ISym (Intro b) a)
    | VLamTy ISym (Scope ISym (Intro' a) b)
    | VCoerce (Elim b a)
    | VErr Err

newtype Intro' a b = Intro' { unIntro' :: Intro b a }

overIntro' :: (Intro b a -> Intro d c) -> Intro' a b -> Intro' c d
overIntro' = coerce

-- | '0 =lim' is extracted from a hypothesis, \(A\!\downarrow\).
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

instance ToSyntax b => Applicative (Intro b) where
    pure = VCoerce . pure
    (<*>) = ap

instance ToSyntax b => Monad (Intro b) where
    return = pure

    (>>=) :: forall a c. Intro b a -> (a -> Intro b c) -> Intro b c
    VLam n t b       >>= k = VLam n t (b >>>= k)
    VCoerce u        >>= k = valueAppBind u k
    VErr err         >>= _ = VErr err
    VLamTy n b       >>= k = undefined n b k

{- VLamTy n $ (overScopeH . overIntro') (>>= k') b where
        k' :: a -> Intro (Var ISym(Mono b)) c
        k' = first (return . return) . k
-}

valueAppBind :: ToSyntax b => Elim b a -> (a -> Intro b c) -> Intro b c
valueAppBind (VVar a) k     = k a
valueAppBind (VApp f x) k   = valueApp (valueAppBind f k) (x >>= k)
valueAppBind (VAppTy f t) k = valueAppTy (valueAppBind f k) t

instance ToSyntax b => Applicative (Elim b) where
    pure = VVar
    (<*>) = ap

instance ToSyntax b => Monad (Elim b) where
    return = pure

    VVar x     >>= k = k x
    VApp f x   >>= k = VApp (f >>= k) (valueBind x k)
    VAppTy x t >>= k = VAppTy (x >>= k) t

valueBind :: ToSyntax b => Intro b a -> (a -> Elim b c) -> Intro b c
valueBind (VCoerce e)  k = VCoerce (e >>= k)
valueBind (VLam n t b) k = VLam n t (b >>>= VCoerce . k)
valueBind (VErr err)   _ = VErr err
valueBind (VLamTy n b) k = VLamTy n $ toScope
    $ Intro'
    $ flip valueBind (first F . k)
    $ unIntro'
    $ fromScope b

instance Module (Intro' a) Mono where
    Intro' i >>== k = Intro' (bindIntroMono i k)

bindIntroMono :: Intro b a -> (b -> Mono c) -> Intro c a
bindIntroMono (VErr err)   _ = VErr err
bindIntroMono (VCoerce c)  k = VCoerce (bindElimMono c k)
bindIntroMono (VLam n t b) k = VLam n (t >>= k) $ hoistScope (`bindIntroMono` k) b

bindIntroMono (VLamTy n (Scope (Intro' b))) k = VLamTy n $ Scope $ Intro' $
    bindIntroMono b $ \v -> case v of
        B x -> return (B x)
        F y -> fmap F (k y)
        

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
    bitraverse _ _ (VErr err)   = pure (VErr err)
    bitraverse f g (VCoerce x)  = VCoerce <$> bitraverse f g x
    bitraverse f g (VLam n t b) = VLam n
        <$> traverse f t
        <*> bitraverseScope f g b
  
    bitraverse f g (VLamTy n b) = VLamTy n
        <$> bitraverseScope g f b

instance Bitraversable Elim where
    bitraverse _ g (VVar a)     = VVar <$> g a
    bitraverse f g (VApp x y)   = VApp <$> bitraverse f g x <*> bitraverse f g y
    bitraverse f g (VAppTy x y) = VAppTy <$> bitraverse f g x <*> traverse f y

-------------------------------------------------------------------------------
-- V application
-------------------------------------------------------------------------------

-- | Apply to values.
--
-- Note that '@@' from "Language.PTSmart" module is different
valueApp
    :: ToSyntax b
    => Intro b a  -- ^ f : a -> b
    -> Intro b a  -- ^ x : a
    -> Intro b a  -- ^ _ : b
valueApp (VCoerce f)  x = VCoerce (VApp f x)
valueApp (VErr err)   _ = VErr err
valueApp (VLam _ _ b) x = instantiate1 x b
valueApp f            _ = VErr (ApplyPanic (toSyntax' (void f)))

valueAppTy
    :: ToSyntax b
    => Intro b a
    -> Mono b
    -> Intro b a
valueAppTy (VCoerce x)  t = VCoerce (VAppTy x t)
valueAppTy (VErr err)   _ = VErr err
valueAppTy (VLamTy _ b) t = instantiate1Mono t b
valueAppTy f            _ = VErr (ApplyPanic (toSyntax' (void f)))

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

instance Eq b => Eq1 (Intro b) where
    liftEq eq (VCoerce x)  (VCoerce x')  = liftEq eq x x'
    liftEq eq (VLam _ t x)   (VLam _ t' x') = liftEq eq x x' && t == t'
    liftEq eq (VLamTy _ b) (VLamTy _ b') = liftEq eq
        (unIntro' $ fromScope b)
        (unIntro' $ fromScope b')

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
-- Show
-------------------------------------------------------------------------------

instance Show2 Intro where
    liftShowsPrec2 _sp _sl _zp _zl d (VErr err) = showsUnaryWith
        showsPrec
        "VErr" d err
    liftShowsPrec2 sp sl zp zl d (VCoerce x) = showsUnaryWith
        (liftShowsPrec2 sp sl zp zl)
        "VCoerce" d x
    -- TODO: type
    liftShowsPrec2 sp sl zp zl d (VLam x _ (Scope y)) = showsBinaryWith
        showsPrec
        (liftShowsPrec2 sp sl (liftShowsPrec zp zl) (liftShowList zp zl))
        "VLam" d x y
    liftShowsPrec2 sp sl zp zl d (VLamTy x (Scope y)) = showsBinaryWith
        showsPrec
        (liftShowsPrec2 zp zl (liftShowsPrec sp sl) (liftShowList sp sl))
        "VLamTy" d x y

instance Show2 Intro' where
    liftShowsPrec2 sp sl zp zl d (Intro' x) = showParen (d >= 10)
        $ liftShowsPrec2 zp zl sp sl 11 x

instance Show2 Elim where
    liftShowsPrec2 _sp _sl zp _zl d (VVar x) = showsUnaryWith
        zp
        "VVar" d x
    liftShowsPrec2 sp sl zp zl d (VApp x y) = showsBinaryWith
        (liftShowsPrec2 sp sl zp zl)
        (liftShowsPrec2 sp sl zp zl)
        "VApp" d x y
    liftShowsPrec2 sp sl zp zl d (VAppTy x y) = showsBinaryWith
        (liftShowsPrec2 sp sl zp zl)
        (liftShowsPrec sp sl)
        "VAppTy" d x y

instance (Show a, Show b) => Show (Intro a b)  where showsPrec = showsPrec2
instance (Show a, Show b) => Show (Intro' a b) where showsPrec = showsPrec2
instance (Show a, Show b) => Show (Elim a b)   where showsPrec = showsPrec2
    
-------------------------------------------------------------------------------
-- ToSyntax
-------------------------------------------------------------------------------

instance (ToSyntax a, ToSyntax b) => ToSyntax (Intro a b) where
    toSyntax x = bitraverse toSyntax toSyntax x >>= toSyntaxIntro

instance (ToSyntax a, ToSyntax b) => ToSyntax (Elim a b) where
    toSyntax x = bitraverse toSyntax toSyntax x >>= toSyntaxElim

toSyntaxIntro :: Intro Syntax Syntax -> SyntaxM
toSyntaxIntro (VErr _err)  = error "some error!"
toSyntaxIntro (VCoerce x)  = toSyntaxElim x
toSyntaxIntro (VLam (ISym n) t b) = freshen n $ \s -> sfn
    (sthe (toSyntaxMono t) (ssym s))
    (toSyntaxIntro (instantiate1return (SSym s) b))
toSyntaxIntro (VLamTy (ISym n) b) = freshen n $ \s -> spoly
    (ssym s)
    (toSyntaxIntro (instantiate1MonoReturn (SSym s) b))

toSyntaxElim :: Elim Syntax Syntax -> SyntaxM
toSyntaxElim (VVar v)     = return v
toSyntaxElim (VApp f x)   = sapp (toSyntaxElim f) (toSyntaxIntro x)
toSyntaxElim (VAppTy x t) = sappTy (toSyntaxElim x) (toSyntaxMono t)

-------------------------------------------------------------------------------
-- instantiate variants
-------------------------------------------------------------------------------

instantiate1Mono :: Mono b -> Scope n (Intro' a) b -> Intro b a
instantiate1Mono t (Scope (Intro' s)) = bindIntroMono s k where
    k (B _) = t
    k (F y) = return y

instantiate1MonoReturn :: b -> Scope n (Intro' a) b -> Intro b a
instantiate1MonoReturn t (Scope (Intro' s)) = first k s where
    k (B _) = t
    k (F y) = y

instantiate1return :: Functor f => a -> Scope n f a -> f a
instantiate1return x (Scope s) = fmap k s where
    k (B _) = x
    k (F a) = a

-------------------------------------------------------------------------------
-- Smart
-------------------------------------------------------------------------------

instance IsString a => IsString (Intro b a) where
    fromString = VCoerce . fromString

instance IsString a => IsString (Elim b a) where
    fromString = VVar . fromString
