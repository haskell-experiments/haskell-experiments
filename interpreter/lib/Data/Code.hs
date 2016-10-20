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
module Data.Code where

import Control.Applicative
-- import Control.Category
-- import Control.Lens hiding (from,to,withIndex,(#=),elements)
-- import Control.Lens.Extras
import Control.Monad
-- import Control.Monad.Free
-- import Control.Monad.State hiding (get)

import Data.Expr.Fix
import Data.Scope

-- import Data.Bifunctor
-- import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.Either.Validation
-- import Data.Functor.Contravariant
import Data.List as L
import Data.Map as M hiding (foldl',foldr)
-- import Data.Semigroup (Semigroup)
import Data.Singletons.Prelude.Enum
import Data.String
-- import Data.Tuple
import Data.Type.Natural hiding ((:-),(:+:),(:*:))

import Prelude hiding ((.),id)

-- import GHC.Generics (Generic,Generic1)
import Proof.Propositional
-- import Test.QuickCheck hiding (Failure,Success,shuffle)

infixr :-

data Stack n where
    Null :: Stack 'Z
    (:-) :: Int -> Stack n -> Stack ('S n)

data Code n where
    ADD  :: Code ('S n) -> Code ('S ('S n))
    SUBTRACT :: Code ('S n) -> Code ('S ('S n))
    NEGATE :: Code ('S n) -> Code ('S n)
    MULT :: Code ('S n) -> Code ('S ('S n))
    PUSH :: Int -> Code ('S n) -> Code n
    POP  :: Code n -> Code ('S n)
    RETURN  :: Code ('S n) -> Code ('S ('S n))
    ABS  :: Code ('S n) -> Code ('S n)
    SIGNUM  :: Code ('S n) -> Code ('S n)
    FETCH   :: Var -> Code ('S n) -> Code n
    GET     :: IsTrue ('S m :<= n) -> SNat m -> Code ('S n) -> Code n
    HALT    :: Code N1

instance Show (Code n) where
    show (ADD c) = "ADD\n" ++ show c
    show (SUBTRACT c) = "SUBTRACT\n" ++ show c
    show (NEGATE c)   = "NEGATE\n" ++ show c
    show (MULT c)   = "MULT\n" ++ show c
    show (PUSH n c) = "PUSH " ++ show n ++ "\n" ++ show c
    show (ABS c) = "ABS\n" ++ show c
    show (SIGNUM c) = "SIGNUM\n" ++ show c
    -- show (STORE v c) = "STORE " ++ v ++ "\n" ++ show c
    show (FETCH (V v) c) = "FETCH " ++ v ++ "\n" ++ show c
    show (GET _ n c) = "GET " ++ show (sNatToInt n :: Int) ++ "\n" ++ show c
    show (POP c) = "POP\n" ++ show c
    show (RETURN c) = "RETURN\n" ++ show c
    show HALT = "HALT"

exec :: Map Var Int
     -> Code 'Z 
     -> Eval Int
exec m c = exec' m c Null

exec' :: Map Var Int
      -> Code n 
      -> Stack n 
      -> Eval Int
exec' m (ADD c) (x :- y :- ys)      = exec' m c ( (x+y) :- ys )
exec' m (SUBTRACT c) (x :- y :- ys) = exec' m c ( (y-x) :- ys )
exec' m (NEGATE c) (y :- ys) = exec' m c ( (-y) :- ys )
exec' m (MULT c) (x :- y :- ys) = exec' m c ( (x*y) :- ys )
exec' m (ABS c)    (y :- ys)  = exec' m c ( abs y :- ys )
exec' m (SIGNUM c) (y :- ys)  = exec' m c ( signum y :- ys )
-- exec' m (STORE v c) (x :- xs) = exec' (M.insert v x m) c xs
exec' m (FETCH v c) xs
    | Just n <- M.lookup v m = exec' m c ( n :- xs )
    | otherwise = Failure ["Variable not bound: " ++ name v]
exec' m (PUSH n c) xs               = exec' m c ( n :- xs )
exec' m (POP c) (_ :- xs)           = exec' m c xs
exec' m (RETURN c) (x :- _ :- xs)   = exec' m c (x :- xs)
exec' m (GET p n c) xs              = exec' m c (get p n xs :- xs)
exec' _ HALT (n :- Null)            = pure n
        -- case s :: Stack (S (S n)) of 
        --     (x :- y :- xs) -> exec c ((x+y) :- xs)

data MyLeq m n where
    LeqRefl :: SNat m -> MyLeq m m
    LeqStep :: SNat m -> MyLeq m n -> MyLeq m ('S n)

leqS :: SNat n -> MyLeq n ('S n)
leqS n = LeqStep n $ LeqRefl n

leqTrans' :: SNat m -> MyLeq m n -> MyLeq n k -> MyLeq m k
leqTrans' _ p (LeqRefl _) = p
leqTrans' m p (LeqStep _ q) = LeqStep m $ leqTrans' m p q

leqSS :: MyLeq n m -> MyLeq ('S n) ('S m)
leqSS (LeqRefl n)   = LeqRefl $ sSucc n
leqSS (LeqStep n p) = LeqStep (sSucc n) $ leqSS p
        -- p :: MyLeq ('S n) m 
        -- _ :: MyLeq ('S ('S n)) ('S ('S n))
        -- leqSS _ p :: MyLeq ('S ('S n)) ('S m)

leqStepR :: SNat n -> MyLeq ('S n) m -> MyLeq n m
leqStepR n p = leqTrans' n (leqS n) p

toMyLeq :: Leq m n -> MyLeq m n
toMyLeq (ZeroLeq SZ) = LeqRefl SZ
toMyLeq (ZeroLeq (SS n)) = LeqStep SZ $ toMyLeq $ ZeroLeq n
toMyLeq (SuccLeqSucc p) = leqSS $ toMyLeq p

get' :: MyLeq ('S n) m
     -> Stack m -> Int
get' (LeqRefl _) (x :- _) = x
get' (LeqStep _ p) (_ :- xs) = get' p xs

get :: IsTrue ('S n :<= m) 
    -> SNat n -> Stack m -> Int
get Witness n s = get' (toMyLeq $ boolToPropLeq (sSucc n) m) s
    where
        m = sLength s

sLength :: Stack n -> SNat n
sLength Null = SZ
sLength (_ :- xs) = SS $ sLength xs

newtype Fetch (m :: Nat) v = Fetch 
        { unFetch :: forall (n :: Nat). 
                           SNat n
                        -> IsTrue (m :<= n) 
                        -> v 
                        -> Code ('S n) 
                        -> Code n }

withIndex :: SingI n
          => (SNat n -> Code (Succ n) -> Code n)
          -> (Code (Succ n) -> Code n)
withIndex f = f sing

bumpFetch :: SNat n
          -> Fetch n v -> Fetch ('S n) v
bumpFetch n (Fetch f) = Fetch $ \m p -> f m (leqSuccStepL n m p) 

instance (Compilable f,Compilable g) => Compilable (f :+: g) where
    compile' f n fetch (L e) = compile' f n fetch e
    compile' f n fetch (R e) = compile' f n fetch e

class Compilable f where
    compile' :: Monad e
             => (forall m u. SNat m
                 -> Fetch m u
                 -> e u
                 -> Code ('S m) 
                 -> Code m)
             -> SNat n
             -> Fetch n v
             -> f e v
             -> Code ('S n) 
             -> Code n

makeFetch :: Fetch ('S n) v -> SNat n -> Fetch ('S n) (Either () v)
makeFetch fetch m = Fetch $ \n p -> either (const $ GET p m) $ unFetch fetch n p

compileFix :: (Compilable f,Lifting HasLit f,IsExpr f)
           => SNat n
           -> Fetch n v
           -> Fix f v
           -> Code ('S n)
           -> Code n
compileFix n fetch (Fix e) = compile' compileFix n fetch e

name :: Var -> String
name (V n) = n
