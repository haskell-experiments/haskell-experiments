{-# LANGUAGE DataKinds,GADTs,DeriveGeneric
        ,TypeSynonymInstances,FlexibleInstances
        ,DeriveFunctor,DeriveFoldable
        ,DeriveTraversable,LambdaCase
        ,PatternSynonyms, PolyKinds
        ,UndecidableInstances
        ,TemplateHaskell
        ,QuasiQuotes
        ,OverloadedStrings
        ,GeneralizedNewtypeDeriving
        ,StandaloneDeriving
        ,MultiParamTypeClasses
        ,ScopedTypeVariables
        ,FlexibleContexts
        ,UndecidableSuperClasses
        ,ConstraintKinds
        ,RankNTypes,KindSignatures
        ,TypeFamilies
        ,TypeOperators #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}
module Data.Scope where

import Control.Applicative
import Control.Category
import Control.Lens hiding (from,to,withIndex,(#=),elements)
import Control.Monad

import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.String

import Prelude hiding ((.),id)

import Test.QuickCheck hiding (Failure,Success,shuffle)

newtype Var = V String
    deriving (Show,Eq,Ord)

newtype Scope b f a = Scope (f (Either b (f a)))
    deriving (Functor,Foldable,Traversable)

instance IsString Var where
    fromString = V

instance (Show a,Show b,Monad f,Lifting Show f) => Show (Scope b f a) where
    show = (show . fromScope)
        C.\\ (lifting :: Show (Either b a) :- Show (f (Either b a)))
instance (Eq a,Eq b,Lifting Eq f,Monad f) => Eq  (Scope b f a) where
    x == y = fromScope x == fromScope y
        C.\\ (lifting :: Eq (Either b a) :- Eq (f (Either b a)))
instance (Ord a,Ord b,Lifting Eq f,Lifting Ord f,Monad f) => Ord (Scope b f a) where
    x `compare` y = fromScope x `compare` fromScope y
        C.\\ (lifting :: Ord (Either b a) :- Ord (f (Either b a)))
    -- Scope x `compare` Scope y = liftCompare (liftCompare . liftCompare $ compare) x y
instance (Arbitrary a,Arbitrary b,Lifting Arbitrary f) => Arbitrary (Scope b f a) where
    arbitrary = Scope <$> arbitrary
        C.\\ (lifting :: Arbitrary (Either b (f a)) :- Arbitrary (f (Either b (f a))))
        C.\\ (lifting :: Arbitrary a :- Arbitrary (f a))

toScope :: Applicative f => f (Either b a) -> Scope b f a 
toScope = Scope . (mapped.mapped %~ pure)

fromScope :: Monad f => Scope b f a -> f (Either b a)
fromScope (Scope x) = join $ sequence <$> x

(>>>=) :: Monad f
       => Scope b f v
       -> (v -> f w)
       -> Scope b f w
(>>>=) (Scope e) f = Scope $ e & mapped._Right %~ (>>= f)

instantiate :: Monad f => Scope () f a -> f a -> f a
instantiate (Scope e) s = e >>= either (const s) id

abstract :: (Applicative f,Eq a) => a -> f a -> Scope () f a
abstract x e = Scope $ f <$> e
    where
        f y | x == y    = Left ()
            | otherwise = Right (pure y)
