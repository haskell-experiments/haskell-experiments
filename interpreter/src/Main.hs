{-# LANGUAGE DataKinds,GADTs,DeriveGeneric
        ,TypeSynonymInstances,FlexibleInstances
        ,DeriveFunctor,DeriveFoldable
        ,DeriveTraversable
        ,MultiParamTypeClasses
        ,ScopedTypeVariables
        ,FlexibleContexts
        ,TypeOperators #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}
module Main where

import Control.Applicative

import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.Either.Validation
import Data.Map as M
import Data.Semigroup
import Data.Type.Natural hiding ((:-))

import GHC.Generics
import Test.QuickCheck hiding (Failure,Success)

infixr :-

newtype Scope b f a = Scope (f (Either b a))
    deriving (Functor,Foldable,Traversable)
instance (Show a,Show b,Lifting Show f) => Show (Scope b f a) where
    show (Scope x) = show x 
        C.\\ (lifting :: Show (Either b a) :- Show (f (Either b a)))
instance (Eq a,Eq b,Lifting Eq f) => Eq  (Scope b f a) where
    Scope x == Scope y = x == y
        C.\\ (lifting :: Eq (Either b a) :- Eq (f (Either b a)))
instance (Ord a,Ord b,Lifting Eq f,Lifting Ord f) => Ord (Scope b f a) where
    Scope x `compare` Scope y = x `compare` y
        C.\\ (lifting :: Ord (Either b a) :- Ord (f (Either b a)))
instance (Arbitrary a,Arbitrary b,Lifting Arbitrary f) => Arbitrary (Scope b f a) where
    arbitrary = Scope <$> arbitrary
        C.\\ (lifting :: Arbitrary (Either b a) :- Arbitrary (f (Either b a)))

type Expr = Expr' String

data Expr' v = Lit Int 
        | Var v
        | Add (Expr' v) (Expr' v)
        | Abs (Expr' v)
        | Signum (Expr' v)
        | Times (Expr' v) (Expr' v)
        | Minus (Expr' v) (Expr' v)
        -- | App (Expr' v) (Expr' v)
        -- | Lam (Scope () Expr' v)
    deriving (Show, Eq, Ord, Generic, Functor, Traversable, Foldable)

instance Lifting Show Expr' where
    lifting = Sub Dict
instance Lifting Eq Expr' where
    lifting = Sub Dict
instance Lifting Ord Expr' where
    lifting = Sub Dict

instance Num Expr where
    (+) = Add
    (-) = Minus
    (*) = Times
    fromInteger = Lit . fromInteger
    abs = Abs
    signum = Signum

instance (Semigroup e,Num a) => Num (Validation e a) where
    (+) = liftA2 (+)
    (-) = liftA2 (-)
    (*) = liftA2 (*)
    abs = fmap abs
    signum = fmap signum
    fromInteger = pure . fromInteger

instance (Num a) => Num (Either e a) where
    (+) = liftA2 (+)
    (-) = liftA2 (-)
    (*) = liftA2 (*)
    abs = fmap abs
    signum = fmap signum
    fromInteger = pure . fromInteger

eval :: Map String Int 
     -> Expr 
     -> Either [String] Int
eval m (Add e0 e1) = eval m e0 + eval m e1
eval m (Minus e0 e1) = eval m e0 - eval m e1
eval m (Times e0 e1) = eval m e0 * eval m e1
eval m (Abs e) = abs <$> eval m e
eval m (Signum e) = signum <$> eval m e
eval m (Var v) = maybe (Left ["Variable not bound: " ++ v]) Right $ M.lookup v m
eval _ (Lit n) = Right n

data Stack n where
    Null :: Stack 'Z
    (:-) :: Int -> Stack n -> Stack ('S n)

data Code n where
    ADD  :: Code ('S n) -> Code ('S ('S n))
    SUBTRACT :: Code ('S n) -> Code ('S ('S n))
    MULT :: Code ('S n) -> Code ('S ('S n))
    PUSH :: Int -> Code ('S n) -> Code n
    ABS  :: Code ('S n) -> Code ('S n)
    SIGNUM  :: Code ('S n) -> Code ('S n)
    FETCH   :: String -> Code ('S n) -> Code n
    HALT    :: Code N1

instance Show (Code n) where
    show (ADD c) = "ADD\n" ++ show c
    show (SUBTRACT c) = "SUBTRACT\n" ++ show c
    show (MULT c) = "MULT\n" ++ show c
    show (PUSH n c) = "PUSH " ++ show n ++ "\n" ++ show c
    show (ABS c) = "ABS\n" ++ show c
    show (SIGNUM c) = "SIGNUM\n" ++ show c
    show (FETCH v c) = "FETCH " ++ v ++ "\n" ++ show c
    show HALT = "HALT"

exec :: Map String Int
     -> Code n 
     -> Stack n 
     -> Either [String] Int
exec m (ADD c) (x :- y :- ys)      = exec m c ( (x+y) :- ys )
exec m (SUBTRACT c) (x :- y :- ys) = exec m c ( (y-x) :- ys )
exec m (MULT c) (x :- y :- ys) = exec m c ( (x*y) :- ys )
exec m (ABS c)    (y :- ys) = exec m c ( abs y :- ys )
exec m (SIGNUM c) (y :- ys) = exec m c ( signum y :- ys )
exec m (FETCH v c) xs              
    | Just n <- M.lookup v m = exec m c ( n :- xs )
    | otherwise = Left ["Variable not bound: " ++ v]
exec m (PUSH n c) xs               = exec m c ( n :- xs )
exec _ HALT (n :- Null)            = Right n
        -- case s :: Stack (S (S n)) of 
        --     (x :- y :- xs) -> exec c ((x+y) :- xs)

compile' :: Expr -> Code ('S n) -> Code n
compile' (Lit n) c = PUSH n c
compile' (Var v) c = FETCH v c
compile' (Abs e) c = compile' e $ ABS c
compile' (Signum e) c  = compile' e $ SIGNUM c
compile' (Add e0 e1) c = compile' e0 . compile' e1 $ ADD c
compile' (Minus e0 e1) c = compile' e0 . compile' e1 $ SUBTRACT c
compile' (Times e0 e1) c = compile' e0 . compile' e1 $ MULT c

compile :: Expr -> Code 'Z
compile e = compile' e HALT

prop_consistent_compilation :: Map String Int -> Expr -> Property
prop_consistent_compilation m e = exec m (compile e) Null === eval m e

instance Lifting Arbitrary Expr' where
    lifting = Sub Dict
instance Arbitrary a => Arbitrary (Expr' a) where
    arbitrary = sized $ \n -> do
            oneof $ 
                [ Lit <$> arbitrary
                , Var <$> arbitrary ]
                ++ if n == 0 then []
                   else  [ resize (n `div` 2) $ Add <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Minus  <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Times  <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Abs    <$> arbitrary 
                         , resize (n `div` 2) $ Signum <$> arbitrary ]
    shrink = genericShrink

main :: IO ()
main = do 
        quickCheck prop_consistent_compilation
        let a = Var "a"
            b = Var "b"
        print $ eval (fromList [("a",3),("b",7)]) $ 3 * a + b
        print $ compile $ 3 * a + b


