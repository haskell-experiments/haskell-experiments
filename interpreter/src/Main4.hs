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
module Main where

import Control.Applicative
import Control.Category
import Control.Lens hiding (from,to,withIndex,(#=),elements)
-- import Control.Lens.Extras
import Control.Monad
-- import Control.Monad.Free
import Control.Monad.State hiding (get)

import Data.Expr.Fix
import Data.Scope

import Data.Bifunctor
import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.Either.Validation
import Data.Functor.Contravariant
import Data.List as L
import Data.Map as M hiding (foldl',foldr)
import Data.Semigroup (Semigroup)
import Data.Singletons.Prelude.Enum
import Data.String
import Data.Tuple
import Data.Type.Natural hiding ((:-),(:+:),(:*:))

import Prelude hiding ((.),id)

import GHC.Generics (Generic,Generic1)
import Proof.Propositional
import Test.QuickCheck hiding (Failure,Success,shuffle)
-- import Text.Printf

data BaseE expr v =
    Lit' Int
    | Var' v 
    deriving (Generic,Generic1,Functor,Foldable,Traversable)
data ArithE expr v =
    Abs' (expr v)
    | Signum' (expr v)
    | Add'    (expr v) (expr v)
    | Times'  (expr v) (expr v)
    | Minus'  (expr v) (expr v)
    deriving (Generic,Generic1,Functor,Foldable,Traversable)

deriving instance (Eq v,Eq (expr v),Lifting Eq expr,Monad expr) => Eq (BaseE expr v)
deriving instance (Ord v,Ord (expr v),Lifting Eq expr,Monad expr) => Ord (BaseE expr v)
deriving instance (Show v,Show (expr v),Lifting Show expr,Monad expr) => Show (BaseE expr v)

deriving instance (Eq v,Eq (expr v),Lifting Eq expr,Monad expr) => Eq (ArithE expr v)
deriving instance (Ord v,Ord (expr v),Lifting Eq expr,Monad expr) => Ord (ArithE expr v)
deriving instance (Show v,Show (expr v),Lifting Show expr,Monad expr) => Show (ArithE expr v)


makePrisms ''BaseE
makePrisms ''ArithE

type Expr = Expr' Var
type Expr' = Fix (BaseE :+: ArithE :+: LetE)
type Expr0' = Fix (BaseE :+: ArithE)

instance (Monad e,Lifting Eq e) => Lifting Eq (LetE e) where
    lifting = weaken2 . liftingLift (Sub Dict)


instance LiftWith Monad (Lifting Eq) LetE where
    lifting' = Sub Dict

instance (Monad e,Lifting Show e) => Lifting Show (LetE e) where
    lifting = weaken2 . liftingLift (Sub Dict)

instance LiftWith Monad (Lifting Show) LetE where
    lifting' = Sub Dict

useLift :: forall c e. Lifting c LetE
        => (c e, Monad e) :- c (LetE e)
useLift = unmapDict $ \Dict -> Dict
            C.\\ (lifting :: c e :- c (LetE e))

instance Lifting Functor LetE where
    lifting = Sub Dict

pattern Lit :: Int -> Expr' v
pattern Lit v = Fix (L (L (Lit' v)))
pattern Var :: v -> Expr' v
pattern Var v = Fix (L (L (Var' v)))
pattern Abs :: Expr' v -> Expr' v
pattern Abs v = Fix (L (R (Abs' v)))
pattern Signum :: Expr' v -> Expr' v
pattern Signum v = Fix (L (R (Signum' v)))
pattern Add :: Expr' v -> Expr' v -> Expr' v
pattern Add x y  = Fix (L (R (Add' x y)))
pattern Times :: Expr' v -> Expr' v -> Expr' v
pattern Times x y  = Fix (L (R (Times' x y)))
pattern Minus :: Expr' v -> Expr' v -> Expr' v
pattern Minus x y  = Fix (L (R (Minus' x y)))
pattern Let :: Scope () Expr' v -> Expr' v -> Expr' v
pattern Let x y    = Fix (R (Let' x y))

data LetE expr v = Let' (Scope () expr v) (expr v)
    deriving (Generic,Generic1,Functor,Foldable,Traversable)

deriving instance (Eq v,Eq (expr v),Lifting Eq expr,Monad expr) => Eq (LetE expr v)
deriving instance (Ord v,Ord (expr v),Lifting Eq expr,Lifting Ord expr,Monad expr) => Ord (LetE expr v)
deriving instance (Show v,Show (expr v),Lifting Show expr,Monad expr) => Show (LetE expr v)

infixr :-

liftingLift :: Lifting c f
            => (c (f a), c a) :- c (g f a)
            -> c a :- (c (f a),c (g f a))
liftingLift f = (weaken1 &&& f) . (lifting &&& id)

class (p a, q a) => (&) p q (a :: k) where

-- data (&) :: (k -> Constraint) -> (k -> Constraint) -> k -> Constraint where
--     Both :: p a -> q a -> (&) p q a

-- data (&) p q a :: Constraint = both (p a) (q a)

instance (Monad f,Lifting Show f) => Lifting Show (BaseE f) where
    lifting = weaken2 . liftingLift (Sub Dict)
instance (Monad f,Lifting Show f) => Lifting Show (ArithE f) where
    lifting = weaken2 . liftingLift (Sub Dict)
instance LiftWith Monad (Lifting Show) BaseE where
    lifting' = Sub Dict
instance LiftWith Monad (Lifting Show) ArithE where
    lifting' = Sub Dict
    -- lifting = weaken2 . liftingLift (Sub Dict)
        -- C.\\ (lifting :: Show a :- Show (f a))
instance LiftWith Monad (Lifting Eq) BaseE where
    lifting' = Sub Dict
instance LiftWith Monad (Lifting Eq) ArithE where
    lifting' = Sub Dict
instance LiftWith (Monad & Lifting Eq) (Lifting Ord) BaseE where
    lifting' = Sub Dict
instance LiftWith (Monad & Lifting Eq) (Lifting Ord) ArithE where
    lifting' = Sub Dict
instance (Lifting Eq f,Monad f) => Lifting Eq (BaseE f) where
    lifting = weaken2 . liftingLift (Sub Dict)
instance (Lifting Eq f,Monad f) => Lifting Eq (ArithE f) where
    lifting = weaken2 . liftingLift (Sub Dict)
instance (Lifting Eq f,Lifting Ord f,Monad f) => Lifting Ord (BaseE f) where
    lifting = weaken2 . liftingLift (Sub Dict)
instance (Lifting Eq f,Lifting Ord f,Monad f) => Lifting Ord (ArithE f) where
    lifting = weaken2 . liftingLift (Sub Dict)
instance Lifting Functor BaseE where
    lifting = Sub Dict
instance Lifting Functor ArithE where
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

-- 132 Young street 

instance HasLit (BaseE f) where
    _Lit = _Lit'
    _Var = _Var'
instance Lifting HasLit BaseE where
    lifting = Sub Dict

instance IsExpr ArithE where
    eval' f _ (Add' e0 e1) = f e0 + f e1
    eval' f _ (Minus' e0 e1) = f e0 - f e1
    eval' f _ (Times' e0 e1) = f e0 * f e1
    eval' f _ (Abs' e) = abs <$> f e
    eval' f _ (Signum' e)  = signum <$> f e
    joinE (Add' e0 e1) = Left (Add' (joinF e0) (joinF e1))
    joinE (Times' e0 e1) = Left (Times' (joinF e0) (joinF e1))
    joinE (Minus' e0 e1) = Left (Minus' (joinF e0) (joinF e1))
    joinE (Abs' e)     = Left (Abs' (joinF e))
    joinE (Signum' e)  = Left (Signum' (joinF e))
    pretty' f n (Add' e0 e1) i = showParen (n > 4) $ 
            f 5 e0 i . showString " + " . f 4 e1 i
    pretty' f n (Minus' e0 e1) i = showParen (n > 4) $ 
            f 5 e0 i . showString " - " . f 5 e1 i
    pretty' f n (Times' e0 e1) i = showParen (n > 5) $ 
            f 6 e0 i . showString " * " . f 5 e1 i
    pretty' f n (Abs' e) i = showParen (n > 6) $ 
            showString "abs " . f 7 e i
    pretty' f n (Signum' e) i = showParen (n > 6) $ 
            showString "signum " . f 7 e i
instance IsExpr BaseE where
    eval' _ m (Var' v@(V n)) = maybe (Failure ["Variable not bound: " ++ n]) pure $ M.lookup v m
    eval' _ _ (Lit' n) = pure n
    joinE (Lit' v)     = Left (Lit' v)
    joinE (Var' e)     = Right e
    pretty' _ _ (Lit' n) _ = 
            shows n
    pretty' _ _ (Var' v) _ = 
            showString (name v)

instance IsExpr LetE where
    eval' f _ (Let' e0 e1) = eitherToValidation $ 
        validationToEither . f . instantiate e0 . mkLit =<< validationToEither (f e1)
    joinE (Let' (Scope e0) e1) = Left (Let' (Scope $ fmap (fmap joinF) e0) (joinF e1))
    pretty' f n (Let' e0 e1) i = showParen (n > 0) $
              showString "let x" . shows i 
            . showString " = " . f 1 e1 (i+1) 
            . showString " in " 
            . f 0 (instantiate e0 $ pure $ V $ "x" ++ show i) (i + 1)

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
    FETCH   :: Var -> Code ('S n) -> Code n
    GET     :: IsTrue ('S m :<= n) -> SNat m -> Code ('S n) -> Code n
    HALT    :: Code N1

instance Show (Code n) where
    show (ADD c) = "ADD\n" ++ show c
    show (SUBTRACT c) = "SUBTRACT\n" ++ show c
    show (MULT c) = "MULT\n" ++ show c
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

name :: Var -> String
name (V n) = n

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
instance Compilable BaseE where
    compile' _ _ _ (Lit' n) = PUSH n
    compile' _ m (Fetch fetch) (Var' v) = fetch m (leqRefl m) v
instance Compilable ArithE where
    compile' f m fetch (Abs' e) = f m fetch e . ABS
    compile' f m fetch (Signum' e)  = f m fetch e . SIGNUM
    compile' f m fetch (Add' e0 e1) = f m fetch e0 . f (sSucc m) (bumpFetch m fetch) e1 . ADD
    compile' f m fetch (Minus' e0 e1) = f m fetch e0 . f (sSucc m) (bumpFetch m fetch) e1 . SUBTRACT
    compile' f m fetch (Times' e0 e1) = f m fetch e0 . f (sSucc m) (bumpFetch m fetch) e1 . MULT
instance Compilable LetE where
    compile' f m fetch (Let' e0 e1)   = f m fetch e1 . f (sSucc m) (makeFetch (bumpFetch m fetch) m) (fromScope e0) . RETURN
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

compile :: Expr -> Code 'Z
compile e = compileFix SZ (Fetch $ \_ _ -> FETCH) e HALT

(<==) :: (Eq a,Show a) 
      => Eval a 
      -> Eval a 
      -> Property
(<==) (Success x) (Success y) = x === y
(<==) (Failure _) _ = property True
-- (<==) (Failure x) (Failure y) = counterexample (show y ++ " /subset " ++ show x)
        -- $ subset (sort y) (sort x)
(<==) (Success x) (Failure y) = 
        counterexample (show x) $
        counterexample (show y) $
            property False

prop_consistent_compilation :: Map Var Int -> Pretty Expr -> Property
prop_consistent_compilation m (Pretty e) = eval m e <== exec m (compile e)

prop_consistent_cse :: Map Var Int -> Pretty Expr -> Property
prop_consistent_cse m (Pretty e) = counterexample (pretty $ elimCommSubexpr e) $
    eval m e <== eval m (elimCommSubexpr e) 

prop_consistent_inlining :: Map Var Int -> Pretty Expr -> Property
prop_consistent_inlining m (Pretty e) = counterexample (pretty $ inline' e) $
    eval m e <== eval m (inline' e)

-- instance Arbitrary Unary where
--     arbitrary = elements [minBound .. maxBound]
-- instance Arbitrary Operator where
--     arbitrary = elements [minBound .. maxBound]
-- instance Lifting Arbitrary (BaseE f) where
--     lifting = Sub Dict
-- instance Arbitrary (BaseE f a) where

instance Applicative Id where
    pure _ = Id 0
    Id x <*> Id y = Id $ x + y

instance Monad Id where
    return _ = Id 0
    Id n >>= _ = Id n

newtype Id a = Id { unId :: Int } 
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Contravariant Id where
    contramap _ (Id n) = Id n

instance Lifting Eq Id where
    lifting = Sub Dict
instance Lifting Ord Id where
    lifting = Sub Dict
instance Lifting Show Id where
    lifting = Sub Dict

type M v = State (Map ((BaseE :+: ArithE) Id v) (Id v,Int)) 

makeId :: Ord v => (BaseE :+: ArithE) Id v -> M v (Id v)
makeId e = do
    gets (M.lookup e) >>= \case
        Just (i,_)  -> do
            ix e._2 += 1
            return i
        Nothing -> do
            i <- gets $ Id . M.size
            modify $ M.insert e (i,1)
            return i

-- elimDeadCode 

elimCommSubexpr :: (Ord v,Show v) => Expr' v -> Expr' v
elimCommSubexpr e = inline e' m' M.empty
    where
        (e',m) = runState (cse' $ inline' e) M.empty
        m' = fromList $ L.map (swap . shuffle . second swap) $ toList m

shuffle :: (a,(b,c)) -> ((a,b),c)
shuffle = uncurry $ uncurry <$> fmap (,) . (,)

cse' :: Ord v
     => Expr0' v
     -> M v (Id v)
cse' (Fix (L (Lit' n))) = makeId $ L $ Lit' n
cse' (Fix (L (Var' v))) = makeId $ L $ Var' v
cse' (Fix (R (Abs' e))) = do
    makeId . R . Abs' =<< cse' e
cse' (Fix (R (Signum' e))) = do
    makeId . R . Signum' =<< cse' e
cse' (Fix (R (Add' e0 e1))) = do
    makeId . R =<< liftA2 Add' (cse' e0) (cse' e1)
cse' (Fix (R (Times' e0 e1))) = do
    makeId . R =<< liftA2 Times' (cse' e0) (cse' e1)
cse' (Fix (R (Minus' e0 e1))) = do
    makeId . R =<< liftA2 Minus' (cse' e0) (cse' e1)

instance Monomorphic BaseE where
    mapRec g _ = \case
        Lit' v -> Lit' v
        Var' v -> Var' (g v)
instance Monomorphic ArithE where
    mapRec _ f = \case
        Abs' e -> Abs' (f e)
        Signum' e    -> Signum' (f e)
        Add' e0 e1   -> Add' (f e0) (f e1)
        Times' e0 e1 -> Times' (f e0) (f e1)
        Minus' e0 e1 -> Minus' (f e0) (f e1)

inline' :: Expr' v -> Expr0' v
inline' (Fix (L e)) = Fix $ mapRec id inline' e
inline' (Fix (R (Let' b l))) = inline' $ instantiate b l

inline :: Show v
       => Id (w :: *) 
       -> Map (Id w) ((BaseE :+: ArithE) Id v, Int) 
       -> Map (Id w) (Expr' v) 
       -> Expr' v
inline n m m0 = case minViewWithKey m of 
    Just ((k,(e,i)),m') 
        | i > 1 && _Lit `isn't` e && _Var `isn't` e ->
             Let (Scope $ inline 
                        n
                        (m' & mapped._1 %~ mapRec (Right . mkVar) phantom) 
                        (M.insert k (mkVar $ Left ()) $ mkVar . Right <$> m0)) 
                 (expand e)
        | otherwise -> inline n m' 
                        (M.insert k (expand e) m0)
    Nothing -> m0 .! n
    where
        expand = Fix . L . mapRec id ((m0 .!) . phantom)
        mm .! x | Just y <- M.lookup x mm = y 
                | otherwise               = error $ "foo: " ++ show mm ++ " " ++ show x

instance Lifting Arbitrary Expr' where
    lifting = Sub Dict
instance Arbitrary a => Arbitrary (Expr' a) where
    arbitrary = Fix <$> arbitrary
    shrink = genericShrink
instance (Arbitrary a,Lifting Arbitrary f) => Arbitrary (ArithE f a) where
    arbitrary = sized $ \n -> do
                   oneof [ resize (n `div` 2) $ Add' <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Minus'  <$> arbitrary <*> arbitrary 
                         , resize (n `div` 2) $ Times' <$> arbitrary <*> arbitrary 
                         -- , resize (n `div` 2) $ Lam  <$> arbitrary 
                         , resize (n `div` 2) $ Signum' <$> arbitrary ]
                            C.\\ (lifting :: Arbitrary a :- Arbitrary (f a))
    shrink = genericShrink
                C.\\ (lifting :: Arbitrary a :- Arbitrary (f a))
instance (Arbitrary a,Lifting Arbitrary f) => Arbitrary (BaseE f a) where
    arbitrary = do
            oneof $ 
                [ Lit' <$> arbitrary
                , Var' <$> arbitrary ]
    shrink = genericShrink
                C.\\ (lifting :: Arbitrary a :- Arbitrary (f a))

instance (Lifting Arbitrary f,Arbitrary (f a),Arbitrary a) 
        => Arbitrary (LetE f a) where
    arbitrary = -- sized $ \n -> do
        -- when (n <= 0) $ fail ""
        scale (`div` 2) $ Let' <$> arbitrary <*> arbitrary

infix 1 #=

(#=) :: String
     -> Expr' Var 
     -> Expr' Var
     -> Expr' Var
(#=) n e b = Let (abstract (V n) b) e

bind :: [Expr' Var -> Expr' Var]
     -> Expr' Var 
     -> Expr' Var 
bind xs x = foldr id x xs

main :: IO ()
main = do 
        quickCheck prop_consistent_compilation
        quickCheck prop_consistent_cse
        quickCheck prop_consistent_inlining
        putStrLn " --- "
        let a = Var "a"
            b = Var "b"
        --     c = Var "c"
            -- store = fromList [("a",3),("b",7)]
        --     -- store' = fromList [("",1 :: Int)]
        --     -- e = App (Lam (Add (Var Left ()) (Var Right ""))) (Lit 0)
        --     e = ["a" #= c, "c" #= a + 1] `bind` (3 * a + b + 7 * c)
        -- print $ eval store $ "a" #= 0 $ 3 * a + b
        -- print $ compile $ "a" #= 0 $ 3 * a + b
        -- putStrLn "--------"
        -- print $ eval store $ 3 * a + b
        -- print $ compile $ 3 * a + b
        -- putStrLn "--------"
        -- print $ eval store e
        -- print $ compile e
        -- print $ exec store (compile e)
        let e = a + b
            (e',m) = runState (cse' $ inline' e) M.empty
            m' = fromList $ L.map (swap . shuffle . second swap) $ toList m
        print $ e'
        print $ m
        print $ m'
        print $ inline e' m' M.empty
        print $ elimCommSubexpr $ (a + b) * (a + b)
        putStrLn $ pretty $ elimCommSubexpr $ abs (a + b + 1 + 3) * (a + b)
        putStrLn " --- "
        print $ compile $ elimCommSubexpr $ abs (a + b + 1 + 3) * (a + b)
        putStrLn " --- "
        print $ compile $ abs (a + b + 1 + 3) * (a + b)


-- next 
-- * dead code removal
-- * scope restrictions
-- * constant folding
-- * if-then-else
-- * rename expression types to BaseE, ArithE, LetE
-- * procedure
