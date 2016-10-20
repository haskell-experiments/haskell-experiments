
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
module Data.Expr.Fix where

import Control.Applicative
import Control.Category
import Control.Lens hiding (from,to,withIndex,(#=),elements)
import Control.Monad

import Data.Scope
import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.Either.Validation
import Data.Map as M hiding (foldl',foldr)
import Data.Proxy.TH
import Data.String
import Data.Type.Natural hiding ((:-),(:+:),(:*:))

import Prelude hiding ((.),id)

import GHC.Generics (Generic,Generic1)

import Test.QuickCheck hiding (Failure,Success,shuffle)

newtype Fix f v = Fix { unFix :: f (Fix f) v }
    deriving (Generic,Generic1)

data (:+:) x y (a :: k0) (b :: k1) = L (x a b) | R (y a b)
    deriving (Eq,Show,Ord,Generic,Generic1)

makePrisms ''(:+:)

instance Lifting (Lifting Eq) f => Lifting Eq (Fix f) where
    lifting = Sub Dict

instance (Eq v,Lifting (Lifting Eq) f) => Eq (Fix f v) where
    Fix x == Fix y = x == y
        C.\\ (lifting :: Eq v :- Eq (f (Fix f) v))
        C.\\ (lifting :: Lifting Eq (Fix f) :- Lifting Eq (f (Fix f)))

instance (Lifting (Lifting Ord) f,Lifting (Lifting Eq) f) 
        => Lifting Ord (Fix f) where
    lifting = Sub Dict

instance (Ord v,Lifting (Lifting Eq) f,Lifting (Lifting Ord) f) => Ord (Fix f v) where
    Fix x `compare` Fix y = x `compare` y
        C.\\ (lifting :: Ord v :- Ord (f (Fix f) v))
        C.\\ (lifting :: Lifting Ord (Fix f) :- Lifting Ord (f (Fix f)))

instance (IsExpr f,Lifting Functor f,Lifting HasLit f,LiftWith Monad (Lifting Show) f) 
        => Lifting Show (Fix f) where
    lifting = Sub Dict

instance (Lifting Functor f,Lifting Functor g) 
        => Lifting Functor (f :+: g) where
    lifting = Sub Dict
instance (Functor e,Lifting Functor f,Lifting Functor g) 
        => Functor ((f :+: g) (e :: * -> *)) where
    fmap f (L x) = L $ fmap f x
                C.\\ (lifting :: Functor e :- Functor (f e))
    fmap f (R x) = R $ fmap f x
                C.\\ (lifting :: Functor e :- Functor (g e))

instance (IsExpr f,Lifting Functor f,Lifting HasLit f,LiftWith Monad (Lifting Show) f,Show v) 
        => Show (Fix f (v :: *)) where
    showsPrec n (Fix x) = showParen (n > 10) $ 
            showString "Fix " . showsPrec 11 x
            C.\\ (lifting :: Show v :- Show (f (Fix f) v))
            C.\\ (lifting' :: (Lifting Show (Fix f),Monad (Fix f)) :- Lifting Show (f (Fix f)))
instance Lifting Functor f => Functor (Fix f) where
    fmap f (Fix x) = Fix $ fmap f x
                C.\\ (lifting :: Functor (Fix f) :- Functor (f (Fix f)))
instance Lifting Foldable f => Foldable (Fix f) where
    foldMap f (Fix x) = foldMap f x
                C.\\ (lifting :: Foldable (Fix f) :- Foldable (f (Fix f)))
instance (Lifting Functor f,Lifting Foldable f,Lifting Traversable f) 
        => Traversable (Fix f) where
    traverse f (Fix x) = Fix <$> traverse f x
                C.\\ (lifting :: Traversable (Fix f) :- Traversable (f (Fix f)))

instance (Lifting Eq e,Monad e,LiftWith Monad (Lifting Eq) f,LiftWith Monad (Lifting Eq) g) 
        => Lifting Eq ((f :+: g) (e :: * -> *)) where
    lifting = myLift' (Sub Dict) . myLift
            C.\\ (lifting' :: (Lifting Eq e,Monad e) :- Lifting Eq (f e))
            C.\\ (lifting' :: (Lifting Eq e,Monad e) :- Lifting Eq (g e))

instance (Lifting Ord e,Lifting (Lifting Ord) f,Lifting (Lifting Ord) g) 
        => Lifting Ord ((f :+: g) (e :: * -> *)) where
    lifting = myLift' (Sub Dict) . myLift
            C.\\ (lifting :: Lifting Ord e :- Lifting Ord (f e))
            C.\\ (lifting :: Lifting Ord e :- Lifting Ord (g e))

instance (Lifting Show e,Monad e,LiftWith Monad (Lifting Show) f,LiftWith Monad (Lifting Show) g) 
        => Lifting Show ((f :+: g) (e :: * -> *)) where
    lifting = myLift' (Sub Dict) . myLift
            C.\\ (lifting' :: (Lifting Show e,Monad e) :- Lifting Show (f e))
            C.\\ (lifting' :: (Lifting Show e,Monad e) :- Lifting Show (g e))

type Eval = Validation [String]

class Lifting Functor expr => IsExpr expr where
    eval' :: (Monad f,HasLit f)
          => (f Var -> Eval Int)
          -> Map Var Int 
          -> expr f Var
          -> Eval Int
    joinE :: IsExpr f 
          => expr (Fix f) (Fix f a) 
          -> Either (expr (Fix f) a)
                    (Fix f a)
    pretty' :: Monad f
            => (Int -> f Var -> Int -> ShowS)
            -> Int -> expr f Var -> Int -> ShowS

instance (IsExpr f,IsExpr g) => IsExpr (f :+: g) where
    eval' f m (L x) = eval' f m x
    eval' f m (R x) = eval' f m x
    joinE (L x) = joinE x & _Left %~ L
    joinE (R x) = joinE x & _Left %~ R
    pretty' f n (L x) = pretty' f n x
    pretty' f n (R x) = pretty' f n x

class HasLit f where
    _Lit :: Prism' (f v) Int
    _Var :: Prism' (f v) v

instance HasLit (f e) => HasLit ((f :+: g) e) where
    _Lit = _L._Lit
    _Var = _L._Var
instance Lifting HasLit f => Lifting HasLit (f :+: g) where
    lifting = Sub Dict . idC [pr|f|] . lifting

joinF :: IsExpr f => Fix f (Fix f a) -> Fix f a
joinF (Fix x) = either Fix id $ joinE x

mkLit :: HasLit f => Int -> f v
mkLit = review _Lit

mkVar :: HasLit f => v -> f v
mkVar = review _Var

pretty :: (Lifting HasLit expr,IsExpr expr)
       => Fix expr Var -> String
pretty e = prettyAux 0 e 0 ""

prettyAux :: (Lifting HasLit expr,IsExpr expr)
          => Int -> Fix expr Var -> Int -> ShowS
prettyAux n (Fix e) i = pretty' prettyAux n e i

instance (IsExpr f,Lifting Functor f,Lifting HasLit f) => Applicative (Fix f) where
    pure = Fix . mkVar
            C.\\ (lifting :: HasLit (Fix f) :- HasLit (f (Fix f)))
    (<*>) = ap
instance (IsExpr f,Lifting Functor f,Lifting HasLit f) => Monad (Fix f) where
    x >>= f = joinF $ f <$> x
instance Lifting HasLit f => HasLit (Fix f) where
    _Lit = iso unFix Fix . _Lit
            C.\\ (lifting :: HasLit (Fix f) :- HasLit (f (Fix f)))
    _Var = iso unFix Fix . _Var
            C.\\ (lifting :: HasLit (Fix f) :- HasLit (f (Fix f)))

eval :: (IsExpr f,Lifting HasLit f)
     => Map Var Int 
     -> Fix f Var
     -> Eval Int
eval m (Fix e) = eval' (eval m) m e

instance (LiftWith Monad (Lifting Eq) f,LiftWith Monad (Lifting Eq) g)
        => LiftWith Monad (Lifting Eq) (f :+: g) where
    lifting' = Sub Dict

instance (Lifting (Lifting Ord) f,Lifting (Lifting Ord) g)
        => Lifting (Lifting Ord) (f :+: g) where
    lifting = Sub Dict

instance (LiftWith Monad (Lifting Show) f,LiftWith Monad (Lifting Show) g)
        => LiftWith Monad (Lifting Show) (f :+: g) where
    lifting' = Sub Dict

class LiftWith p (c :: k -> Constraint) f where
    lifting' :: (c a, p a) :- c (f a)

myLift :: forall a c e f g. (Lifting c (f e),Lifting c (g e))
       => c (a :: *) :- (c a,c (f e a),c (g e a))
myLift = unmapDict $ \Dict -> Dict
            C.\\ (lifting :: c a :- c (f e a))
            C.\\ (lifting :: c a :- c (g e a))

myLift' :: (c a,c (f e a),c (g e a)) :- c ((:+:) f g e a)
        -> (c a,c (f e a),c (g e a)) :- c ((:+:) f g e a)
myLift' = id

idC :: Proxy f -> c (f a) :- c (f a)
idC _ = id

instance (Lifting HasLit expr,IsExpr expr) => Show (Pretty (Fix expr Var)) where
    show = pretty . unPretty

class Monomorphic f where 
    mapRec :: (v0 -> v1)
           -> (expr0 v0 -> expr1 v1)
           -> f expr0 v0
           -> f expr1 v1

instance (Monomorphic f,Monomorphic g) => Monomorphic (f :+: g) where
    mapRec g f (L x) = L $ mapRec g f x
    mapRec g f (R x) = R $ mapRec g f x

instance (Arbitrary (p f a),Arbitrary (q f a)) => Arbitrary ((p :+: q) f a) where
    -- arbitrary = oneof [L <$> arbitrary]
    arbitrary = sized $ \n -> 
        if n == 0 
            then L <$> arbitrary
            else oneof [L <$> arbitrary,R <$> arbitrary]
    shrink = genericShrink

instance Arbitrary Var where
    arbitrary = V <$> sequence [elements ['a'..'z']]

newtype Pretty a = Pretty { unPretty :: a }
    deriving (Generic,Eq,Ord)

instance Arbitrary a => Arbitrary (Pretty a) where
    arbitrary = Pretty <$> arbitrary
    shrink = genericShrink
