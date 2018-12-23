-- |
--
-- The code here is a modification of part of @unification-fd@ package.
--
-- @
-- Copyright (c) 2007, 2008, 2011, 2012, 2013, 2014, wren gayle romano.
-- ALL RIGHTS RESERVED.
-- 
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
-- 
--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.
-- 
--     * Neither the name of the copyright holders nor the names of
--       other contributors may be used to endorse or promote products
--       derived from this software without specific prior written
--       permission.
-- 
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
-- FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
-- COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
-- INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
-- BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
-- LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
-- LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
-- ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
-- POSSIBILITY OF SUCH DAMAGE.
-- @
--
module OL1.Unify (
    -- * Term
    UTerm (..),
    -- * Unifiable
    Unifiable (..),
    -- * Errors
    Fallible (..),
    RigidFallible (..),
    RigidFallibleAll (..),
    -- * Monad
    Unify,
    runUnify,
    freeVar,
    -- * Variable
    MetaVar (..),
    Variable,
    RigidVariable,
    -- * Unification
    unify,
    applyBindings,
    applyBindingsAll,
    withRigid,
    )where

import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity (Identity (..))
import Data.Traversable      (for)

import qualified Data.IntMap as IM

-------------------------------------------------------------------------------
-- MetaVar
-------------------------------------------------------------------------------

newtype MetaVar = MetaVar Int
  deriving (Eq, Ord, Show)

class Eq v => Variable v where
    mkMetaVar     :: Int -> v
    matchMetaVar' :: v -> Maybe Int

class Variable v => RigidVariable n v where
    matchMetaVar :: v -> Either n Int

instance Variable MetaVar where
    mkMetaVar                 = MetaVar
    matchMetaVar' (MetaVar i) = Just i

instance RigidVariable n MetaVar where
    matchMetaVar (MetaVar i) = Right i

instance (Eq n, Variable v) => Variable (Either n v) where
    mkMetaVar     = Right . mkMetaVar
    matchMetaVar' = either (const Nothing) matchMetaVar'

instance (Eq n, RigidVariable n v) => RigidVariable n (Either n v) where
    matchMetaVar (Left n)  = Left n
    matchMetaVar (Right v) = matchMetaVar v

-------------------------------------------------------------------------------
-- Term
-------------------------------------------------------------------------------

data UTerm t v
    = UVar  !v               -- ^ A unification variable.
    | UTerm !(t (UTerm t v)) -- ^ Some structure containing subterms.

instance Functor t => Functor (UTerm t) where
    fmap f (UVar  v) = UVar  (f v)
    fmap f (UTerm t) = UTerm (fmap (fmap f) t)

instance Foldable t => Foldable (UTerm t) where
    foldMap f (UVar  v) = f v
    foldMap f (UTerm t) = foldMap (foldMap f) t

instance Traversable t => Traversable (UTerm t) where
    traverse f (UVar  v) = UVar  <$> f v
    traverse f (UTerm t) = UTerm <$> traverse (traverse f) t

-------------------------------------------------------------------------------
-- Unifiable
-------------------------------------------------------------------------------

class Traversable t => Unifiable t where
    zipMatch :: t a -> t a -> Maybe (t (Either a (a, a)))

-------------------------------------------------------------------------------
-- Error
-------------------------------------------------------------------------------

class Variable v => Fallible t v e where
    occursFailure        :: v -> UTerm t v -> e
    mismatchFailure      :: t (UTerm t v) -> t (UTerm t v) -> e

class RigidFallible n e where
    rigidMismatchFailure :: n -> n -> e
    escapingRigidFailure :: n -> e

class (Fallible t v e, RigidFallible n e, RigidVariable n v) => RigidFallibleAll n t v e where
    rigidBindFailure     :: n -> t (UTerm t v) -> e

-------------------------------------------------------------------------------
-- Basic methods
-------------------------------------------------------------------------------

lookupVar
    :: (Variable v, RigidFallible n e)
    => v -> Unify n e t v (Maybe (UTerm t v))
lookupVar v = case matchMetaVar' v of
    Nothing  -> return Nothing
    Just i -> Unify $ do
        m <- gets (IM.lookup i . varBindings)
        for m $ \m' -> case m' of
            Left sko -> throwError $ escapingRigidFailure sko
            Right t  -> return t

freeVar :: Variable v => Unify n e t v v
freeVar = Unify $ do
    ibs <- get
    let v = nextFreeVar ibs
    if  v == maxBound
        then error "freeVar: no more variables!"
        else do
            put $ ibs { nextFreeVar = v+1 }
            return $ mkMetaVar v

bindVar
    :: forall n e t v. (RigidFallibleAll n t v e, RigidVariable n v)
    => v -> UTerm t v -> Unify n e t v ()
bindVar v t = case matchMetaVar v :: Either n Int of
    Left n  -> case t of
        UVar _   -> return () -- this is not right
        UTerm t' -> throwError $ rigidBindFailure n t'
    Right i -> Unify $ do
        ibs <- get
        let bs' = IM.insert i (Right t) (varBindings ibs)
        put $ ibs { varBindings = bs' }

-------------------------------------------------------------------------------
-- Unification
-------------------------------------------------------------------------------

semiprune
    :: (RigidFallibleAll n t v e, RigidVariable n v)
    => UTerm t v -> Unify n e t v (UTerm t v)
semiprune t0'@(UTerm _ )  = return t0'
semiprune t0'@(UVar  v0') = loop t0' v0' where
    -- We pass the @t@ for @v@ in order to add just a little more sharing.
    loop t0 v0 = do
        mb <- lookupVar v0
        case mb of
            Nothing -> return t0
            Just t  ->
                case t  of
                UTerm _  -> return t0
                UVar  v  -> do
                    finalVar <- loop t v
                    v0 `bindVar` finalVar
                    return finalVar

unify
    :: forall t v e n. (Unifiable t, RigidFallibleAll n t v e)
    => UTerm t v -> UTerm t v -> Unify n e t v (UTerm t v)
unify tl0' tr0' = evalStateT (loop tl0' tr0') IM.empty
    where
    {-# INLINE (=:) #-}
    v =: t = lift $ v `bindVar` t

    equalVars :: v -> v -> Unify n e t v ()
    equalVars a b
        | a == b    = return ()
        | otherwise = case (matchMetaVar a :: Either n Int, matchMetaVar b) of
            (Right _, _)       -> bindVar a (UVar b)
            (_,       Right _) -> bindVar b (UVar a)
            (Left a', Left b') -> throwError $ rigidMismatchFailure a' b'

    loop :: UTerm t v -> UTerm t v -> StateT (IM.IntMap (t (UTerm t v))) (Unify n e t v) (UTerm t v)
    loop tl00 tr00 = do
        tl0 <- lift $ semiprune tl00
        tr0 <- lift $ semiprune tr00
        case (tl0, tr0) of
            (UVar vl, UVar vr)
                | vl == vr  -> return tr0
                | otherwise -> do
                    mtl <- lift $ lookupVar vl
                    mtr <- lift $ lookupVar vr
                    case (mtl, mtr) of
                        (Nothing, Nothing) -> do lift (equalVars vl vr) ; return tr0
                        (Nothing, Just _ ) -> do vl =: tr0 ; return tr0
                        (Just _ , Nothing) -> do vr =: tl0 ; return tl0
                        (Just (UTerm tl), Just (UTerm tr)) -> do
                            t <- localState $ do
                                vl `seenAs` tl
                                vr `seenAs` tr
                                match tl tr
                            vr =: t
                            vl =: tr0
                            return tr0
                        _ -> error _impossible_unify

            (UVar vl, UTerm tr) -> do
                t <- do
                    mtl <- lift $ lookupVar vl
                    case mtl of
                        Nothing         -> return tr0
                        Just (UTerm tl) -> localState $ do
                            vl `seenAs` tl
                            match tl tr
                        _ -> error _impossible_unify
                vl =: t
                return tl0

            (UTerm tl, UVar vr) -> do
                t <- do
                    mtr <- lift $ lookupVar vr
                    case mtr of
                        Nothing         -> return tl0
                        Just (UTerm tr) -> localState $ do
                            vr `seenAs` tr
                            match tl tr
                        _ -> error _impossible_unify
                vr =: t
                return tr0

            (UTerm tl, UTerm tr) -> match tl tr

    match tl tr =
        case zipMatch tl tr of
        Nothing  -> lift . Unify . throwError $ mismatchFailure tl tr
        Just tlr -> UTerm <$> traverse loop_ tlr

    loop_ (Left  t)       = return t
    loop_ (Right (tl,tr)) = loop tl tr

applyBindings :: (Traversable t, RigidFallibleAll n t v e) => UTerm t v -> Unify n e t v (UTerm t v)
applyBindings = fmap runIdentity . applyBindingsAll . Identity

applyBindingsAll
    :: forall t s v e n. (Traversable s, Traversable t, RigidFallibleAll n t v e)
    => s (UTerm t v) -> Unify n e t v (s (UTerm t v))
applyBindingsAll ts0 = evalStateT (traverse loop ts0) IM.empty where
    loop :: UTerm t v -> StateT (IM.IntMap (Either (UTerm t v) (UTerm t v))) (Unify n e t v) (UTerm t v)
    loop t0_ = do
        t0 <- lift $ semiprune t0_
        case t0 of
            UTerm t -> UTerm <$> traverse loop t
            UVar  v -> case matchMetaVar' v of
                Nothing -> return t0
                Just i  -> do
                    mb <- IM.lookup i <$> get
                    case mb of
                        Just (Right t) -> return t
                        Just (Left  t) -> lift . throwError $ occursFailure v t
                        Nothing -> do
                            mb' <- lift $ lookupVar v
                            case mb' of
                                Nothing -> return t0
                                Just t  -> do
                                    modify' . IM.insert i $ Left t
                                    t' <- loop t
                                    modify' . IM.insert i $ Right t'
                                    return t'

_impossible_unify :: String
{-# NOINLINE _impossible_unify #-}
_impossible_unify = "unify: the impossible happened"

seenAs
    :: forall n e t v. (Variable v, Fallible t v e)
    => v
    -> t (UTerm t v) -- ^
    -> StateT (IM.IntMap (t (UTerm t v))) (Unify n e t v) () -- ^
{-# INLINE seenAs #-}
seenAs v0 t0 = case matchMetaVar' v0 of
    Nothing -> return ()
    Just i  -> do
        seenVars <- get
        case IM.lookup i seenVars of
            Just t  -> lift . Unify . throwError $ occursFailure v0 (UTerm t)
            Nothing -> put $! IM.insert i t0 seenVars

-------------------------------------------------------------------------------
-- Skolem
-------------------------------------------------------------------------------

withRigid :: Traversable t => Unify n e t (Either n v) a -> Unify n e t v a
withRigid (Unify m) = Unify $ ExceptT $ StateT $ \st0 -> do
    let (x, st1) = runState (runExceptT m) (fmap Right st0)
        vb       = fmap (>>= sequence) (varBindings st1)
    return (x, st1 { varBindings = vb })

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

data St n t v = St
    { nextFreeVar :: {-# UNPACK #-} !Int
    , varBindings :: IM.IntMap (Either n (UTerm t v))
    }
  deriving Functor

emptySt :: St n t v
emptySt = St minBound IM.empty

newtype Unify n e t v a = Unify { unUnify :: ExceptT e (State (St n t v)) a }
  deriving newtype (Functor, Applicative, Monad, MonadError e)

runUnify :: Unify n e t v a -> Either e a
runUnify m = evalState (runExceptT (unUnify m)) emptySt

-------------------------------------------------------------------------------
-- Misc
-------------------------------------------------------------------------------

-- | Run a state action and undo the state changes at the end.
localState :: (MonadState s m) => m a -> m a
{-# INLINE localState #-}
localState m = do
    s <- get
    x <- m
    put s
    return x
