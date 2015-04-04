{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances #-}
module UniversalRankOne where

import Prelude hiding (elem, lookup, mapM_)

import Control.Applicative
import Control.Exception
import Control.Monad.Except hiding (mapM_)
import Control.Monad.State.Lazy hiding (mapM_)
import Data.Data
import Data.Foldable
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
import Data.Typeable ()

import Debug.Trace

type Offset = Int
type Length = Int

data SrcPos = SrcPos Offset Length | NoWhere
  deriving (Data, Eq, Ord, Read, Show, Typeable)

data GenType a
  = Function SrcPos (GenType a) (GenType a)
  | Named SrcPos String
  | Variable SrcPos a
  deriving (Data, Eq, Foldable, Functor, Ord, Read, Show, Typeable)

type Type = GenType String

instance Applicative GenType where
  pure = Variable NoWhere
  mf <*> mt = do
    f <- mf
    t <- mt
    return (f t)

instance Monad GenType where
  return = Variable NoWhere
  (>>=) = genTypeBind

genTypeBind t f =
    case t of
      Function sp t1 t2 -> Function sp (t1 >>= f) (t2 >>= f)
      Named sp s -> Named sp s
      Variable _ x -> f x

bind :: TypeCheck m => String -> Type -> m ()
bind v t =
  case t of
    Variable _ v' | v == v' -> return ()
    _ -> do
      when (elem v t) $ throwError (OccursCheck v t)
      modify (mapTypeCheckState (replace v t))
      modifySubstitutions (M.insert v t)

mapTypeCheckState f (cs, ss) = (fmap (mapConstraint f) cs, fmap f ss) where
  mapConstraint f (Constraint c1 c2) = Constraint (f c1) (f c2)

newtype MappableState a = MappableState { unMappableState :: ([(GenType a, GenType a)], M.Map String (GenType a)) }
  deriving (Functor)

unify :: (TypeCheck m) => m ()
unify = do
  cs <- popConstraint
  case cs of
    Nothing -> return ()
    Just (Constraint s t) ->
      case (s,t) of
        (Variable _ v, t) -> bind v t >> unify
        (t, Variable _ v) -> bind v t >> unify
        (Named _ a, Named _ b)
          | a == b -> unify
          | otherwise -> throwError (Unequal s t)
        (Function _ si so, Function _ ti to) -> do
          addConstraint si ti
          addConstraint so to
          unify
        _ -> throwError $ Unequal s t

tr :: (Monad m, Show s) => String -> s -> m ()
tr s v = traceM (s ++ ": " ++ show v)

popConstraint = do
  (cs, ss) <- get
  case cs of
    [] -> return Nothing
    (x:xs) -> do
      put (xs, ss)
      return (Just x)

modifySubstitutions :: TypeCheck m => (M.Map String Type -> M.Map String Type) -> m ()
modifySubstitutions f = modify (\(cs, ss) -> (cs, f ss))

addConstraint c1 c2 = modify (\(cs, ss) -> (Constraint c1 c2 :cs, ss))

replace :: (Eq a) => a -> GenType a -> GenType a -> GenType a
replace var t = (subst var t =<<)

subst :: (Monad m, Eq a) => a -> m a -> a -> m a
subst var t v | v == var = t
              | otherwise = return v

data Constraint a = Constraint (GenType a) (GenType a)
  deriving (Data, Eq, Foldable, Functor, Ord, Read, Show, Typeable)

expand :: String -> Type -> Bindings -> Type
expand var binding bindings = e (S.singleton var) binding where
  e blacklist t =
    case t of
      Variable _ v'
        | elem v' blacklist -> t
        | otherwise ->
            case M.lookup v' bindings of
              Nothing -> t
              Just t' -> e (S.insert v' blacklist) t'
      Named _ _ -> t
      Function sp input output -> Function sp (e blacklist input) (e blacklist output)

data TypeError
  = Unequal Type Type
  | NotAFunction Type
  | OccursCheck String Type
  deriving (Data, Eq, Ord, Read, Show, Typeable)

instance Exception TypeError

class (MonadState TypeCheckState m, MonadError TypeError m) => TypeCheck m where

type Bindings = M.Map String Type
type Constraints = [Constraint String]
type TypeCheckState = (Constraints, Bindings)

newtype TypeCheckM m a = TypeCheckM { unTypeCheckM :: (ExceptT TypeError (StateT TypeCheckState m) a) }
  deriving (Applicative, Functor, Monad, MonadError TypeError, MonadState TypeCheckState)

instance Monad m => TypeCheck (TypeCheckM m)

runTypeCheckM :: (Monad m) => TypeCheckM m a -> Constraints -> m (Either TypeError a, Bindings)
runTypeCheckM m cs = do
  (a, (_, bindings)) <- flip runStateT (cs, mempty) . runExceptT . unTypeCheckM $ m
  return (a, bindings)

uni :: (Monad m) => Type -> Type -> m (Maybe TypeError, Bindings)
uni c1 c2 = do
  (e, b) <- runTypeCheckM unify [Constraint c1 c2]
  case e of
    Left ee -> return (Just ee, b)
    Right () -> return (Nothing, b)

t = do
  let sp = SrcPos 0 0
      named = Named sp
      function = Function sp
      variable = Variable sp
      [a, b, c] = fmap variable ["a","b","c"]
      [s, t] = fmap named ["s", "t"]
  mapM_ assertNoErrors [
    uni (named "MyType") (named "MyType"),
    uni (function s t) (function s t)]
  assertError (Unequal s t) $ uni s t
  assertError (Unequal (function s t) s) $ uni (function s t) s
  assertNoErrors $ uni a s
  assertNoErrors $ uni s a
  assertNoErrors $ uni a b
  assertNoErrors $ uni (function a s) (function t b)
  assertError (Unequal s t) $ uni (function s a) (function t a)
  assertError (OccursCheck "a" (function s a)) $ uni a (function s a)
  assertError (OccursCheck "a" (function s a)) $ uni (function s a) (function s (function s a))
  assertBinding ["a" :-> s] $ uni a s
  assertBinding ["a" :-> s, "b" :-> t] $ uni (function a b) (function s t)
  -- assertBinding ["a" :-> s, "b" :-> t] $ uni (function a t) (function s b)
  -- assertError (Unequal t s) $ uni (function a (function a t)) (function s (function t t))
  -- assertNoErrors $ uni (function a (function a s)) (function c (function s c))
  -- assertError (OccursCheck "a" (function s a)) $ uni (function a (function s a)) (function c c)

assertNoErrors m = do
  (result, _) <- m
  case result of
    Nothing -> return ()
    Just te -> throwIO te

assertError e m = do
  (result, _) <- m
  case result of
    Just te | te == e -> return ()
            | otherwise -> throwIO (Mismatched e te)
    Nothing -> throwIO NoError

data Binding = String :-> Type

assertBinding bindings m = do
  let expected = M.fromList . fmap (\(a :-> b) -> (a,b)) $ bindings
  (result, actual) <- m
  case result of
    Just te -> throwIO te
    Nothing | expected == actual -> return ()
            | otherwise -> throwIO (MismatchedBindings expected actual)
  
data UnexpectedTypeError
  = Mismatched { expected :: TypeError, actual :: TypeError }
  | MismatchedBindings { expectedBindings :: Bindings, actualBindings :: Bindings }
  | NoError
  deriving (Data, Eq, Ord, Read, Show, Typeable)

instance Exception UnexpectedTypeError
