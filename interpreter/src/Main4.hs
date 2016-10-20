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
import Control.Monad
import Control.Monad.State hiding (get)

import Data.Code
import Data.Expr.Fix
import Data.Scope

import Data.Bifunctor
import Data.Constraint as C
import Data.Constraint.Lifting as C
import Data.Either
import Data.Either.Combinators
import Data.Either.Validation
import Data.Foldable as F
import Data.Functor.Contravariant
import Data.List as L
import Data.Map as M hiding (foldl',foldr)
import Data.Maybe
import Data.Semigroup (Semigroup)
import Data.Singletons.Prelude.Enum
import Data.String
import Data.Tuple
import Data.Type.Natural hiding ((:-),(:+:),(:*:))

import Prelude hiding ((.),id)

import GHC.Generics (Generic,Generic1)
import Test.QuickCheck hiding (Failure,Success,shuffle)

data BaseE expr v =
    Lit' Int
    | Var' v 
    deriving (Generic,Generic1,Functor,Foldable,Traversable)
data ArithE expr v =
    Abs' (expr v)
    | Signum' (expr v)
    | Add'    (expr v) (expr v)
    | Neg'    (expr v)
    | Times'  (expr v) (expr v)
    | Minus'  (expr v) (expr v)
    deriving (Generic,Generic1,Functor,Foldable,Traversable)

data ArithAssocE expr v =
    AbsA'      (expr v)
    | SignumA' (expr v)
    | NegA'    (expr v)
    | Sum'     [expr v]
    | Product' [expr v]
    deriving (Generic,Generic1,Functor,Foldable,Traversable)

deriving instance (Eq v,Eq (expr v),Lifting Eq expr,Monad expr) => Eq (BaseE expr v)
deriving instance (Ord v,Ord (expr v),Lifting Eq expr,Monad expr) => Ord (BaseE expr v)
deriving instance (Show v,Show (expr v),Lifting Show expr,Monad expr) => Show (BaseE expr v)

deriving instance (Eq v,Eq (expr v),Lifting Eq expr,Monad expr) => Eq (ArithE expr v)
deriving instance (Ord v,Ord (expr v),Lifting Eq expr,Monad expr) => Ord (ArithE expr v)
deriving instance (Show v,Show (expr v),Lifting Show expr,Monad expr) => Show (ArithE expr v)

deriving instance (Eq v,Eq (expr v),Lifting Eq expr,Monad expr) => Eq (ArithAssocE expr v)
deriving instance (Ord v,Ord (expr v),Lifting Eq expr,Monad expr) => Ord (ArithAssocE expr v)
deriving instance (Show v,Show (expr v),Lifting Show expr,Monad expr) => Show (ArithAssocE expr v)

makePrisms ''BaseE
makePrisms ''ArithE

type Expr = Expr' Var
type Expr' = Fix (BaseE :+: ArithE :+: LetE)
type ExprAssoc' = Fix (BaseE :+: ArithAssocE)
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

instance Lifting Functor ArithAssocE where
    lifting = Sub Dict
instance Lifting Foldable ArithAssocE where
    lifting = Sub Dict

instance Lifting Functor LetE where
    lifting = Sub Dict
instance Lifting Foldable LetE where
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

liftingLift :: Lifting c f
            => (c (f a), c a) :- c (g f a)
            -> c a :- (c (f a),c (g f a))
liftingLift f = (weaken1 &&& f) . (lifting &&& id)

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
instance Lifting Foldable BaseE where
    lifting = Sub Dict
instance Lifting Foldable ArithE where
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

intercalateShow :: ShowS -> (a -> ShowS) -> [a] -> ShowS
intercalateShow _ _ [] = id
intercalateShow _ f [x] = f x
intercalateShow comma f (x0:x1:xs) = f x0 . comma . intercalateShow comma f (x1:xs)

instance IsExpr ArithAssocE where
    eval' f _ (Sum' xs) = sum $ L.map f xs
    eval' f _ (Product' xs) = product $ L.map f xs
    eval' f _ (AbsA' e) = abs <$> f e
    eval' f _ (NegA' e) = negate <$> f e
    eval' f _ (SignumA' e)  = signum <$> f e
    joinE (Sum' es) = Left (Sum' $ L.map joinF es)
    joinE (Product' es) = Left (Product' $ L.map joinF es)
    joinE (NegA' e)     = Left (NegA' (joinF e))
    joinE (AbsA' e)     = Left (AbsA' (joinF e))
    joinE (SignumA' e)  = Left (SignumA' (joinF e))
    pretty' f _ (Sum' es) i = 
            showString "[ " . intercalateShow (showString " + ") (($ i) . f 5) es . showString " ]"
    pretty' f n (NegA' e0) i = showParen (n > 3) $ 
            showString "- " . f 4 e0 i
    pretty' f _ (Product' es) i = 
            showString "[ " . intercalateShow (showString " * ") (($ i) . f 6) es . showString " ]"
    pretty' f n (AbsA' e) i = showParen (n > 6) $ 
            showString "abs " . f 7 e i
    pretty' f n (SignumA' e) i = showParen (n > 6) $ 
            showString "signum " . f 7 e i
instance IsExpr ArithE where
    eval' f _ (Add' e0 e1) = f e0 + f e1
    eval' f _ (Minus' e0 e1) = f e0 - f e1
    eval' f _ (Times' e0 e1) = f e0 * f e1
    eval' f _ (Abs' e) = abs <$> f e
    eval' f _ (Neg' e) = negate <$> f e
    eval' f _ (Signum' e)  = signum <$> f e
    joinE (Add' e0 e1) = Left (Add' (joinF e0) (joinF e1))
    joinE (Times' e0 e1) = Left (Times' (joinF e0) (joinF e1))
    joinE (Minus' e0 e1) = Left (Minus' (joinF e0) (joinF e1))
    joinE (Neg' e)     = Left (Neg' (joinF e))
    joinE (Abs' e)     = Left (Abs' (joinF e))
    joinE (Signum' e)  = Left (Signum' (joinF e))
    pretty' f n (Add' e0 e1) i = showParen (n > 4) $ 
            f 5 e0 i . showString " + " . f 4 e1 i
    pretty' f n (Minus' e0 e1) i = showParen (n > 4) $ 
            f 5 e0 i . showString " - " . f 5 e1 i
    pretty' f n (Neg' e0) i = showParen (n > 3) $ 
            showString "- " . f 4 e0 i
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

instance Compilable BaseE where
    compile' _ _ _ (Lit' n) = PUSH n
    compile' _ m (Fetch fetch) (Var' v) = fetch m (leqRefl m) v
instance Compilable ArithE where
    compile' f m fetch (Abs' e) = f m fetch e . ABS
    compile' f m fetch (Signum' e)  = f m fetch e . SIGNUM
    compile' f m fetch (Add' e0 e1) = f m fetch e0 . f (sSucc m) (bumpFetch m fetch) e1 . ADD
    compile' f m fetch (Neg' e0)    = f m fetch e0 . NEGATE
    compile' f m fetch (Minus' e0 e1) = f m fetch e0 . f (sSucc m) (bumpFetch m fetch) e1 . SUBTRACT
    compile' f m fetch (Times' e0 e1) = f m fetch e0 . f (sSucc m) (bumpFetch m fetch) e1 . MULT
instance Compilable LetE where
    compile' f m fetch (Let' e0 e1)   = f m fetch e1 . f (sSucc m) (makeFetch (bumpFetch m fetch) m) (fromScope e0) . RETURN

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
prop_consistent_compilation m (Pretty e) = 
    counterexample (show $ compile e) $
        eval m e <== exec m (compile e)

prop_consistent_cse :: Map Var Int -> Pretty Expr -> Property
prop_consistent_cse m (Pretty e) = 
    counterexample (pretty $ elimCommSubexpr $ inline' e) $
        eval m e <== eval m (elimCommSubexpr $ inline' e) 

prop_consistent_inlining :: Map Var Int -> Pretty Expr -> Property
prop_consistent_inlining m (Pretty e) = 
    counterexample (pretty $ inline' e) $
        eval m e <== eval m (inline' e)

prop_consistent_cse_inlining :: Map Var Int -> Pretty Expr -> Property
prop_consistent_cse_inlining m (Pretty e) = 
    counterexample (pretty $ inline' e) $
    counterexample (pretty $ elimCommSubexpr $ inline' e) $
        eval m (elimCommSubexpr $ inline' e) === eval m (inline' e)

prop_consistent_constantFolding :: Map Var Int -> Pretty Expr -> Property
prop_consistent_constantFolding m (Pretty e) = 
    counterexample (pretty $ constFolding $ inline' e) $
        eval m e <== eval m (constFolding $ inline' e)

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
constFolding :: Ord v => Expr0' v -> Expr0' v
constFolding = either mkLit id . constFolding' . flattenAssoc

mkSum :: [Expr0' v] -> Either (Maybe Int) (Expr0' v)
mkSum = foldl' (flip mkAdd) (Left Nothing)
-- mkSum [] = Left Nothing
-- mkSum (x:xs) = either (maybe (Right x) (Left . Just)) (Right . Fix . R . Add' x) $ mkSum xs
    where
        mkAdd x = either (maybe (Right x) (Left . Just)) (Right . Fix . R . flip Add' x)

mkProduct :: [Expr0' v] -> Either (Maybe Int) (Expr0' v)
mkProduct = foldl' (flip mkTimes) (Left Nothing)
    where
        mkTimes x = either (maybe (Right x) (Left . Just)) (Right . Fix . R . flip Times' x)

constFolding' :: Ord v
              => ExprAssoc' v 
              -> Either Int (Expr0' v)
constFolding' = iso unFix Fix $ \case
        L (Var' n) -> Right $ L (Var' n)
        L (Lit' n) -> Left $ n
        R (AbsA' e) -> mapBoth abs (R . Abs') $ constFolding' e
        R (SignumA' e) -> mapBoth signum (R . Signum') $ constFolding' e
        R (NegA' e)    -> mapBoth negate (R . Neg') $ constFolding' e
        R (Sum' es) 
                | n == 0 -> mapBoth (fromMaybe 0) unFix $ mkSum ys'
                | L.null ys -> Right $ L $ Lit' n
                | otherwise -> mapBoth (fromMaybe 0) unFix 
                        $ mkSum $ Fix (L $ Lit' n) : ys'
            where
                n = sum xs
                ys' = sort ys
                (xs,ys) = partitionEithers $ L.map constFolding' es
        R (Product' es) 
                | n == 0 -> Right $ L $ Lit' 0
                | n == 1 -> mapBoth (fromMaybe 1) unFix $ mkProduct ys'
                | L.null ys -> Right $ L $ Lit' n
                | otherwise -> mapBoth (fromMaybe 1) unFix 
                        $ mkProduct $ Fix (L $ Lit' n) : ys'
            where
                n = product xs
                ys' = sort ys
                (xs,ys) = partitionEithers $ L.map constFolding' es
        -- R (Times' e0 e1) -> case combine (constFolding' e0) (constFolding' e1) of
        --                     Left (k0,k1)  -> Left (k0*k1)
        --                     Right (e0',e1') -> Right $ R $ Times' e0' e1'
        -- R (Minus' e0 e1) -> case combine (constFolding' e0) (constFolding' e1) of
        --                     Left (k0,k1)  -> Left (k0-k1)
        --                     Right (e0',e1') -> Right $ R $ Minus' e0' e1'

combine :: Lifting HasLit f
        => Either Int (Fix f v)
        -> Either Int (Fix f (v :: *))
        -> Either (Int,Int) (Fix f v,Fix f v)
combine (Right x) (Right y) = Right (x,y)
combine (Left x) (Right y) = Right (mkLit x,y)
combine (Right x) (Left y) = Right (x,mkLit y)
combine (Left x) (Left y)  = Left (x,y)

elimCommSubexpr :: (Ord v,Show v) => Expr0' v -> Expr' v
elimCommSubexpr e = inline e' m' M.empty
    where
        (e',m) = runState (cse' e) M.empty
        m' = fromList $ L.map (swap . shuffle . second swap) $ M.toList m

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
cse' (Fix (R (Neg' e0))) = do
    makeId . R =<< fmap Neg' (cse' e0)

instance Monomorphic BaseE where
    mapRecA g _ = \case
        Lit' v -> pure $ Lit' v
        Var' v -> Var' <$> g v
instance Monomorphic ArithE where
    mapRecA _ f = \case
        Abs' e -> Abs' <$> f e
        Signum' e    -> fmap Signum' (f e)
        Add' e0 e1   -> liftA2 Add' (f e0) (f e1)
        Times' e0 e1 -> liftA2 Times' (f e0) (f e1)
        Minus' e0 e1 -> liftA2 Minus' (f e0) (f e1)
        Neg' e -> fmap Neg' (f e)

inline' :: Expr' v -> Expr0' v
inline' (Fix (L e)) = Fix $ mapRec id inline' e
inline' (Fix (R (Let' b l))) = inline' $ instantiate b l

neg :: ExprAssoc' v -> ExprAssoc' v
neg (Fix (R (NegA' e))) = e
neg e = Fix (R (NegA' e))

flattenSum :: Expr0' v -> [ExprAssoc' v]
flattenSum (Fix (R (Add' x0 x1)))   = flattenSum x0 ++ flattenSum x1
flattenSum (Fix (R (Minus' x0 x1))) = flattenSum x0 ++ L.map neg (flattenSum x1)
flattenSum e = [flattenAssoc e]

flattenProduct :: Expr0' v -> [ExprAssoc' v]
flattenProduct (Fix (R (Times' x0 x1))) = flattenProduct x0 ++ flattenProduct x1
flattenProduct e = [flattenAssoc e]

flattenAssoc :: Expr0' v -> ExprAssoc' v
flattenAssoc (Fix (L (Lit' v))) = Fix (L (Lit' v))
flattenAssoc (Fix (L (Var' v))) = Fix (L (Var' v))
flattenAssoc e@(Fix (R (Add' _ _))) = Fix (R (Sum' $ flattenSum e))
flattenAssoc e@(Fix (R (Minus' _ _))) = Fix (R (Sum' $ flattenSum e))
flattenAssoc e@(Fix (R (Times' _ _))) = Fix (R (Product' $ flattenProduct e))
flattenAssoc (Fix (R (Abs' e)))     = Fix (R (AbsA' $ flattenAssoc e))
flattenAssoc (Fix (R (Signum' e)))  = Fix (R (SignumA' $ flattenAssoc e))
flattenAssoc _ = undefined

inline :: Show v
       => Id (w :: *) 
       -> Map (Id w) ((BaseE :+: ArithE) Id v, Int) 
       -> Map (Id w) (Expr' v) 
       -> Expr' v
inline n m m0 = case minViewWithKey m of 
    Just ((k,(e,_)),m') 
        | occ > 1 && _Lit `isn't` e && _Var `isn't` e ->
             Let (Scope e') 
                 (expand e)
        | otherwise -> inline n m' 
                        (M.insert k (expand e) m0)
        where
            occ = length $ lefts $ F.toList $ e' 
            e' = inline n
                    (m' & mapped._1 %~ mapRec (Right . mkVar) phantom) 
                    (M.insert k (mkVar $ Left ()) $ mkVar . Right <$> m0)
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
    shrink = genericShrink
                C.\\ (lifting :: Arbitrary a :- Arbitrary (f a))

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

return []

main :: IO ()
main = do 
        print =<< $quickCheckAll
        putStrLn " --- "
        let a = Var "a"
            b = Var "b"
            c = Var "c"
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
        let 
            e = "c" #= b + 1 $ abs (a + c + 3) * (b + 4 + a + 1)
            -- (e',m) = runState (cse' $ inline' e) M.empty
            -- m' = fromList $ L.map (swap . shuffle . second swap) $ M.toList m
        print $ elimCommSubexpr $ inline' e
        putStrLn $ pretty e
        putStrLn $ pretty $ elimCommSubexpr $ inline' e
        putStrLn $ pretty $ flattenAssoc $ inline' e
        putStrLn $ pretty $ constFolding $ inline' e
        putStrLn $ pretty $ elimCommSubexpr $ constFolding $ inline' e
        putStrLn " --- "
        print $ compile $ elimCommSubexpr $ constFolding $ inline' e
        putStrLn " --- "
        print $ compile e


-- next 
-- * dead code removal
-- * scope restrictions
-- * if-then-else
-- * procedure

-- * constant folding
-- * rename expression types to BaseE, ArithE, LetE
