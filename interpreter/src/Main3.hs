{-# LANGUAGE DataKinds,GADTs,DeriveGeneric
        ,TypeSynonymInstances,FlexibleInstances
        ,DeriveFunctor,DeriveFoldable
        ,DeriveTraversable
        ,MultiParamTypeClasses
        ,ScopedTypeVariables
        ,FlexibleContexts
        ,RankNTypes
        ,TypeFamilies
        ,TypeOperators #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}
module Main where

import Control.Applicative
import Control.Lens hiding (from,to,withIndex,(#=),elements)
import Control.Monad

import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.Either.Validation
import Data.Map as M hiding ((!),foldl',foldr)
import Data.Monoid
import Data.Semigroup (Semigroup)
import Data.Singletons.Prelude.Enum
import Data.Typeable
import Data.Type.Natural hiding ((:-),(:+:),(:*:))
-- import Data.Type.Natural.Definitions

import GHC.Generics
import Proof.Propositional
import Test.QuickCheck hiding (Failure,Success)
import Text.Printf

infixr :-

newtype Scope b f a = Scope (f (Either b (f a)))
    deriving (Functor,Foldable,Traversable)

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
instance Arbitrary (a :~: a) where
    arbitrary = return Refl

toScope :: Applicative f => f (Either b a) -> Scope b f a 
toScope = Scope . (mapped.mapped %~ pure)

fromScope :: Monad f => Scope b f a -> f (Either b a)
fromScope (Scope x) = join $ sequence <$> x

type Expr = Expr' Int String

data Expr' t v where
    Lit  :: Int -> Expr' Int v
    Var  :: v -> Expr' Int v
    Abs  :: Expr' Int v -> Expr' Int v
    Signum :: Expr' Int v -> Expr' Int v
    Add    :: Expr' Int v -> Expr' Int v -> Expr' Int v
    Times  :: Expr' Int v -> Expr' Int v -> Expr' Int v
    Minus  :: Expr' Int v -> Expr' Int v -> Expr' Int v
    -- App :: Expr' (Int -> Int) v -> Expr' Int v -> Expr' Int v
    Let :: Scope () (Expr' Int) v -> Expr' Int v -> Expr' Int v

-- data Expr' t v =
--     Lit (t :~: Int) Int 
--     | Var (t :~: Int) v
--     | Abs (t :~: Int) (Expr' Int v)
--     | Signum (t :~: Int) (Expr' Int v)
--     | Add (t :~: Int) (Expr' Int v) (Expr' Int v)
--     | Times (t :~: Int) (Expr' Int v) (Expr' Int v)
--     | Minus (t :~: Int) (Expr' Int v) (Expr' Int v)
--     | App (t :~: Int) (Expr' (Int -> Int) v) (Expr' Int v)
--     | Lam (t :~: (Int -> Int)) (Scope () (Expr' Int) v)
--     deriving (Eq,Ord,Show,Functor,Generic)

data Operator = Sum' | Prod | Diff
    deriving (Eq,Show,Ord,Enum,Bounded)
data Unary = AbsOp | SignumOp
    deriving (Eq,Show,Ord,Enum,Bounded)

instance Generic (Expr' t v) where
    type Rep (Expr' t v) = 
            K1 R ((t :~: Int),Int)
            :+: K1 R ((t :~: Int),v)
            :+: (K1 R (t :~: Int) :*: K1 R Operator :*: K1 R (Expr' Int v) :*: K1 R (Expr' Int v))
            :+: (K1 R (t :~: Int) :*: K1 R Unary :*: K1 R (Expr' Int v))
            :+: (K1 R (t :~: Int) :*: K1 R (Scope () (Expr' Int) v) :*: K1 R (Expr' Int v))
    from (Lit v) = L1 $ K1 (Refl,v)
    from (Var v) = R1 $ L1 $ K1 (Refl,v)
    from (Add  e0 e1)  = R1 $ R1 $ L1 $ K1 Refl :*: K1 Sum' :*: K1 e0 :*: K1 e1
    from (Times e0 e1) = R1 $ R1 $ L1 $ K1 Refl :*: K1 Prod :*: K1 e0 :*: K1 e1
    from (Minus e0 e1) = R1 $ R1 $ L1 $ K1 Refl :*: K1 Diff :*: K1 e0 :*: K1 e1
    from (Abs e0)      = R1 $ R1 $ R1 $ L1 $ K1 Refl :*: K1 AbsOp :*: K1 e0
    from (Signum e0)   = R1 $ R1 $ R1 $ L1 $ K1 Refl :*: K1 SignumOp :*: K1 e0
    -- from (Lam e0)      = R1 $ R1 $ R1 $ R1 $ L1 $ K1 Refl :*: K1 e0
    from (Let e0 e1)   = R1 $ R1 $ R1 $ R1 $ K1 Refl :*: K1 e0 :*: K1 e1
    to (L1 (K1 (Refl,v))) = Lit v
    to (R1 (L1 (K1 (Refl,v)))) = Var v
    to (R1 (R1 (L1 (K1 Refl :*: K1 Sum' :*: K1 e0 :*: K1 e1)))) = Add e0 e1
    to (R1 (R1 (L1 (K1 Refl :*: K1 Prod :*: K1 e0 :*: K1 e1)))) = Times e0 e1
    to (R1 (R1 (L1 (K1 Refl :*: K1 Diff :*: K1 e0 :*: K1 e1)))) = Minus e0 e1
    to (R1 (R1 (R1 (L1 (K1 Refl :*: K1 SignumOp :*: K1 e0))))) = Signum e0
    to (R1 (R1 (R1 (L1 (K1 Refl :*: K1 AbsOp :*: K1 e0))))) = Abs e0
    to (R1 (R1 (R1 (R1 (K1 Refl :*: K1 e0 :*: K1 e1))))) = Let e0 e1

type M = 'MetaData "Expr'" "Main" "interpreter" 'True
instance Generic1 (Expr' t) where
    type Rep1 (Expr' t) = 
            K1 R ((t :~: Int),Int)
            :+: (K1 R (t :~: Int) :*: Par1)
            :+: (K1 R (t :~: Int) :*: K1 R Operator :*: S1 M (Expr' Int) :*: S1 M (Expr' Int))
            :+: (K1 R (t :~: Int) :*: K1 R Unary :*: S1 M (Expr' Int))
            :+: (K1 R (t :~: Int) :*: S1 M (Scope () (Expr' Int)) :*: S1 M (Expr' Int))
    from1 (Lit v) = L1 $ K1 (Refl,v)
    from1 (Var v) = R1 $ L1 $ K1 Refl :*: Par1 v
    from1 (Add  e0 e1)  = R1 $ R1 $ L1 $ K1 Refl :*: K1 Sum' :*: M1 e0 :*: M1 e1
    from1 (Times e0 e1) = R1 $ R1 $ L1 $ K1 Refl :*: K1 Prod :*: M1 e0 :*: M1 e1
    from1 (Minus e0 e1) = R1 $ R1 $ L1 $ K1 Refl :*: K1 Diff :*: M1 e0 :*: M1 e1
    from1 (Abs e0)      = R1 $ R1 $ R1 $ L1 $ K1 Refl :*: K1 AbsOp :*: M1 e0
    from1 (Signum e0)   = R1 $ R1 $ R1 $ L1 $ K1 Refl :*: K1 SignumOp :*: M1 e0
    -- from1 (Lam e0)      = R1 $ R1 $ R1 $ R1 $ L1 $ K1 Refl :*: M1 e0
    from1 (Let e0 e1)   = R1 $ R1 $ R1 $ R1 $ K1 Refl :*: M1 e0 :*: M1 e1
    to1 (L1 (K1 (Refl,v))) = Lit v
    to1 (R1 (L1 (K1 Refl :*: Par1 v))) = Var v
    to1 (R1 (R1 (L1 (K1 Refl :*: K1 Sum' :*: M1 e0 :*: M1 e1)))) = Add e0 e1
    to1 (R1 (R1 (L1 (K1 Refl :*: K1 Prod :*: M1 e0 :*: M1 e1)))) = Times e0 e1
    to1 (R1 (R1 (L1 (K1 Refl :*: K1 Diff :*: M1 e0 :*: M1 e1)))) = Minus e0 e1
    to1 (R1 (R1 (R1 (L1 (K1 Refl :*: K1 SignumOp :*: M1 e0))))) = Signum e0
    to1 (R1 (R1 (R1 (L1 (K1 Refl :*: K1 AbsOp :*: M1 e0))))) = Abs e0
    to1 (R1 (R1 (R1 (R1 (K1 Refl :*: M1 e0 :*: M1 e1))))) = Let e0 e1

instance Show v => Show (Expr' t v) where
    show (Lit n) = "Lit " ++ show n
    show (Var v) = "Var " ++ show v
    show (Add e0 e1)   = printf "Add (%s) (%s)" (show e0) (show e1)
    show (Times e0 e1) = printf "Times (%s) (%s)" (show e0) (show e1)
    show (Minus e0 e1) = printf "Minus (%s) (%s)" (show e0) (show e1)
    show (Abs e0) = printf "Abs (%s)" (show e0)
    show (Signum e0) = printf "Signum (%s)" (show e0)
    show (Let e0 e1) = printf "Let (%s) (%s)" (show e0) (show e1)
    -- show (Lam e0) = printf "Lam (%s)" (show e0)

class GEq a where
    gEq :: a p -> a p -> Bool

instance (GEq a,GEq b) => GEq (a :*: b) where
    gEq (x0 :*: x1) (y0 :*: y1) = gEq x0 y0 && gEq x1 y1
instance (GEq a,GEq b) => GEq (a :+: b) where
    gEq (L1 x) (L1 y) = gEq x y
    gEq (R1 x) (R1 y) = gEq x y
    gEq _ _ = True
instance Eq a => GEq (K1 s a) where
    gEq (K1 x) (K1 y) = x == y

class GOrd a where
    gCompare :: a p -> a p -> Ordering

instance (GOrd a,GOrd b) => GOrd (a :*: b) where
    gCompare (x0 :*: x1) (y0 :*: y1) = gCompare x0 y0 <> gCompare x1 y1
instance (GOrd a,GOrd b) => GOrd (a :+: b) where
    gCompare (L1 x) (L1 y) = gCompare x y
    gCompare (R1 x) (R1 y) = gCompare x y
    gCompare (L1 _) (R1 _) = LT
    gCompare (R1 _) (L1 _) = GT
instance Ord a => GOrd (K1 s a) where
    gCompare (K1 x) (K1 y) = x `compare` y

instance Eq v => Eq (Expr' t v) where
    x == y = gEq (from x) (from y)
instance Ord v => Ord (Expr' t v) where
    compare x y = gCompare (from x) (from y)

class GFunctor f where
    fmapG :: (a -> b) -> f a -> f b

instance (GFunctor a,GFunctor b) => GFunctor (a :+: b) where
    fmapG f (L1 x) = L1 $ fmapG f x
    fmapG f (R1 x) = R1 $ fmapG f x
instance (GFunctor a,GFunctor b) => GFunctor (a :*: b) where
    fmapG f (x :*: y) = fmapG f x :*: fmapG f y
instance GFunctor (K1 s a) where
    fmapG _ (K1 x) = K1 x
instance GFunctor Par1 where
    fmapG f (Par1 x) = Par1 $ f x
instance Functor f => GFunctor (M1 s t f) where
    fmapG f (M1 x) = M1 $ f <$> x

class GTraversable t where
    traverseG :: Applicative f => (a -> f b) -> t a -> f (t b)

instance (GTraversable a,GTraversable b) => GTraversable (a :+: b) where
    traverseG f (L1 x) = L1 <$> traverseG f x
    traverseG f (R1 x) = R1 <$> traverseG f x
instance (GTraversable a,GTraversable b) => GTraversable (a :*: b) where
    traverseG f (x :*: y) = (:*:) <$> traverseG f x <*> traverseG f y
instance GTraversable (K1 s a) where
    traverseG _ (K1 x) = pure $ K1 x
instance GTraversable Par1 where
    traverseG f (Par1 x) = Par1 <$> f x
instance Traversable f => GTraversable (M1 s t f) where
    traverseG f (M1 x) = M1 <$> traverse f x

class GFoldable f where
    foldMapG :: Monoid m => (a -> m) -> f a -> m

instance (GFoldable a,GFoldable b) => GFoldable (a :+: b) where
    foldMapG f (L1 x) = foldMapG f x
    foldMapG f (R1 x) = foldMapG f x
instance (GFoldable a,GFoldable b) => GFoldable (a :*: b) where
    foldMapG f (x :*: y) = foldMapG f x <> foldMapG f y
instance GFoldable (K1 s a) where
    foldMapG _ (K1 _) = mempty
instance GFoldable Par1 where
    foldMapG f (Par1 x) = f x
instance Foldable f => GFoldable (M1 s t f) where
    foldMapG f (M1 x) = foldMap f x

instance Functor (Expr' t) where
    fmap f = to1 . fmapG f . from1
instance Foldable (Expr' t) where
    foldMap f = foldMapG f . from1
instance Traversable (Expr' t) where
    traverse f = fmap to1 . traverseG f . from1
instance Applicative (Expr' Int) where
    pure  = return
    (<*>) = ap
instance Monad (Expr' Int) where
    return = Var
    (>>=)  = subst

subst :: Expr' a v 
      -> (v -> Expr' Int w)
      -> Expr' a w
Lit v `subst` _ = Lit v
Var v `subst` f = f v
Add e0 e1 `subst` f   = Add (e0 >>= f) (e1 >>= f)
Times e0 e1 `subst` f = Times (e0 >>= f) (e1 >>= f)
Minus e0 e1 `subst` f = Minus (e0 >>= f) (e1 >>= f)
Abs e `subst` f = Abs $ e >>= f
Signum e `subst` f = Signum $ e >>= f
Let e0 e1 `subst` f = Let (e0 >>>= f) (e1 >>= f)

(>>>=) :: Scope b (Expr' Int) v
       -> (v -> Expr' Int w)
       -> Scope b (Expr' Int) w
(>>>=) (Scope e) f = Scope $ e & mapped._Right %~ (>>= f)


instance Lifting Show (Expr' t) where
    lifting = Sub Dict
instance Lifting Eq (Expr' t) where
    lifting = Sub Dict
instance Lifting Ord (Expr' t) where
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

instantiate :: Monad f => Scope () f a -> f a -> f a
instantiate (Scope e) s = e >>= either (const s) id


eval :: Map String Int 
     -> Expr 
     -> Either [String] Int
eval m (Add e0 e1) = eval m e0 + eval m e1
eval m (Minus e0 e1) = eval m e0 - eval m e1
eval m (Times e0 e1) = eval m e0 * eval m e1
eval m (Let e0 e1) = eval m . instantiate e0 . Lit =<< eval m e1
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
    POP  :: Code n -> Code ('S n)
    RETURN  :: Code ('S n) -> Code ('S ('S n))
    ABS  :: Code ('S n) -> Code ('S n)
    SIGNUM  :: Code ('S n) -> Code ('S n)
    FETCH   :: String -> Code ('S n) -> Code n
    GET     :: IsTrue ('S m :<= n) -> SNat m -> Code ('S n) -> Code n
    STORE   :: String -> Code n -> Code ('S n)
    HALT    :: Code N1

instance Show (Code n) where
    show (ADD c) = "ADD\n" ++ show c
    show (SUBTRACT c) = "SUBTRACT\n" ++ show c
    show (MULT c) = "MULT\n" ++ show c
    show (PUSH n c) = "PUSH " ++ show n ++ "\n" ++ show c
    show (ABS c) = "ABS\n" ++ show c
    show (SIGNUM c) = "SIGNUM\n" ++ show c
    show (STORE v c) = "STORE " ++ v ++ "\n" ++ show c
    show (FETCH v c) = "FETCH " ++ v ++ "\n" ++ show c
    show (GET _ n c) = "GET " ++ show (sNatToInt n :: Int) ++ "\n" ++ show c
    show (POP c) = "POP\n" ++ show c
    show (RETURN c) = "RETURN\n" ++ show c
    show HALT = "HALT"

exec :: Map String Int
     -> Code 'Z 
     -> Either [String] Int
exec m c = exec' m c Null

exec' :: Map String Int
      -> Code n 
      -> Stack n 
      -> Either [String] Int
exec' m (ADD c) (x :- y :- ys)      = exec' m c ( (x+y) :- ys )
exec' m (SUBTRACT c) (x :- y :- ys) = exec' m c ( (y-x) :- ys )
exec' m (MULT c) (x :- y :- ys) = exec' m c ( (x*y) :- ys )
exec' m (ABS c)    (y :- ys)  = exec' m c ( abs y :- ys )
exec' m (SIGNUM c) (y :- ys)  = exec' m c ( signum y :- ys )
exec' m (STORE v c) (x :- xs) = exec' (M.insert v x m) c xs
exec' m (FETCH v c) xs              
    | Just n <- M.lookup v m = exec' m c ( n :- xs )
    | otherwise = Left ["Variable not bound: " ++ v]
exec' m (PUSH n c) xs               = exec' m c ( n :- xs )
exec' m (POP c) (_ :- xs)           = exec' m c xs
exec' m (RETURN c) (x :- _ :- xs)   = exec' m c (x :- xs)
exec' m (GET p n c) xs              = exec' m c (get p n xs :- xs)
exec' _ HALT (n :- Null)            = Right n
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

-- leqSuccStepL' :: (SingI (n :: Nat), SingI (m :: Nat)) 
--               => Sing n -> Sing m -> IsTrue ('S n :<= m) -> IsTrue (n :<= m)
-- leqSuccStepL' = leqSuccStepL :: Sing n -> Sing m -> IsTrue ('S n :<= m) -> IsTrue (n :<= m)

-- succLe :: Sing n -> Sing m -> IsTrue ('S n :<= m) -> IsTrue (n :<= m)
-- succLe _ _ = _
-- succLeL' :: Sing n -> Sing m -> Leq ('S n) m -> Leq n m
-- succLeL' m n (SuccLeqSucc p) = succLeR' m (sPred n) p

-- succLeR' :: Sing n -> Sing m -> Leq n m -> Leq n ('S m)
-- succLeR' n m (SuccLeqSucc p) = SuccLeqSucc $ succLeR' (sPred n) (sPred m) p
-- succLeR' _ _ (ZeroLeq q) = ZeroLeq $ sSucc q

bumpFetch :: SNat n
          -> Fetch n v -> Fetch ('S n) v
bumpFetch n (Fetch f) = Fetch $ \m p -> f m (leqSuccStepL n m p) 

compile' :: SNat n
         -> Fetch n v
         -> Expr' Int v
         -> Code ('S n) 
         -> Code n
compile' _ _ (Lit n) = PUSH n
compile' m (Fetch fetch) (Var v) = fetch m (leqRefl m) v
compile' m fetch (Abs e) = compile' m fetch e . ABS
compile' m fetch (Signum e)  = compile' m fetch e . SIGNUM
compile' m fetch (Add e0 e1) = compile' m fetch e0 . compile' (sSucc m) (bumpFetch m fetch) e1 . ADD
compile' m fetch (Minus e0 e1) = compile' m fetch e0 . compile' (sSucc m) (bumpFetch m fetch) e1 . SUBTRACT
compile' m fetch (Times e0 e1) = compile' m fetch e0 . compile' (sSucc m) (bumpFetch m fetch) e1 . MULT
compile' m fetch (Let e0 e1)   = compile' m fetch e1 . compile' (sSucc m) (makeFetch (bumpFetch m fetch) m) (fromScope e0) . RETURN
    where
        -- fetch' :: _
        -- fetch' = makeFetch fetch

makeFetch :: Fetch ('S n) v -> SNat n -> Fetch ('S n) (Either () v)
makeFetch fetch m = Fetch $ \n p -> either (const $ GET p m) $ unFetch fetch n p



compile :: Expr -> Code 'Z
compile e = compile' SZ (Fetch $ \_ _ -> FETCH) e HALT

prop_consistent_compilation :: Map String Int -> Expr -> Property
prop_consistent_compilation m e = exec m (compile e) === eval m e

instance Arbitrary Unary where
    arbitrary = elements [minBound .. maxBound]
instance Arbitrary Operator where
    arbitrary = elements [minBound .. maxBound]
instance Lifting Arbitrary (Expr' Int) where
    lifting = Sub Dict
instance Arbitrary a => Arbitrary (Expr' Int a) where
    arbitrary = sized $ \n -> do
            oneof $ 
                [ Lit <$> arbitrary
                , Var <$> arbitrary ]
                ++ if n == 0 then []
                   else  [ resize (n `div` 2) $ Add <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Minus  <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Times <$> arbitrary <*> arbitrary 
                         -- , resize (n `div` 2) $ Lam  <$> arbitrary 
                         , resize (n `div` 2) $ Let <$> arbitrary <*> arbitrary
                         , resize (n `div` 2) $ Signum <$> arbitrary ]
    shrink = genericShrink

infix 1 #=

(#=) :: String
     -> Expr' Int String 
     -> Expr' Int String
     -> Expr' Int String
(#=) n e b = Let (abstract n b) e

bind :: [Expr' Int String -> Expr' Int String]
     -> Expr' Int String 
     -> Expr' Int String 
bind xs x = foldr id x xs

abstract :: (Applicative f,Eq a) => a -> f a -> Scope () f a
abstract x e = Scope $ f <$> e
    where
        f y | x == y    = Left ()
            | otherwise = Right (pure y)


main :: IO ()
main = do 
        quickCheck prop_consistent_compilation
        let a = Var "a"
            b = Var "b"
            c = Var "c"
            store = fromList [("a",3),("b",7)]
            -- store' = fromList [("",1 :: Int)]
            -- e = App (Lam (Add (Var Left ()) (Var Right ""))) (Lit 0)
            e = ["a" #= c, "c" #= a + 1] `bind` (3 * a + b + 7 * c)
        print $ eval store $ "a" #= 0 $ 3 * a + b
        print $ compile $ "a" #= 0 $ 3 * a + b
        putStrLn "--------"
        print $ eval store $ 3 * a + b
        print $ compile $ 3 * a + b
        putStrLn "--------"
        print $ eval store e
        print $ compile e
        print $ exec store (compile e)


