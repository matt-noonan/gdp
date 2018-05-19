{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module List where

import           Unsafe.Coerce
import           Data.Coerce
import           Data.Reflection
import           Data.Proxy
import qualified Data.List as L
import           Data.Ord

-- The phantom type can serve as a kind of equality mechanism, even for types
-- that do not support equality.

newtype Filter phi a = Filter (a -> Bool)

newtype Filtered phi a = Filtered a

filter' :: Filter phi a -> [a] -> Filtered phi [a]
filter' (Filter f) xs = Filtered (filter f xs)

withFilter :: (a -> Bool) -> (forall phi. Filter phi a -> t) -> t
withFilter f k = k (coerce f)

commute' :: Filtered phi (Filtered phi' a) -> Filtered phi' (Filtered phi a)
commute' = coerce

flatten :: Filtered phi (Filtered phi a) -> Filtered phi a
flatten = coerce

combine :: Filtered phi (Filtered phi' a) -> Filtered (And phi phi') a
combine = coerce

class Proposition p

data And p q
data Or  p q
data Not p

newtype Property phi a = Value a

type SuchThat a phi = Property phi a

theValue :: Property phi a -> a
theValue (Value x) = x

concat' :: Filtered phi [a] -> Filtered phi [a] -> Filtered phi [a]
concat' (Filtered xs) (Filtered ys) = Filtered (xs ++ ys)

and_intro :: Property p (Property q t) -> Property (And p q) t
and_intro = coerce

and_elimL :: t `SuchThat` And p q -> t `SuchThat` p
and_elimL = coerce

and_elimR :: t `SuchThat` And p q -> t `SuchThat` q
and_elimR = coerce

or_introL :: t `SuchThat` p -> t `SuchThat` Or p q
or_introL = coerce

or_introR :: t `SuchThat` q -> t `SuchThat` Or p q
or_introR = coerce

or_elim :: (t `SuchThat` p -> t' `SuchThat` r)
        -> (t `SuchThat` q -> t' `SuchThat` r)
        -> t `SuchThat` (Or p q)
        -> t' `SuchThat` r
or_elim f _ = f . coerce

class Commutative c where
  commute :: t `SuchThat` c p q -> t `SuchThat` c q p

class Associative c where
  assocL :: t `SuchThat` c p (c q r) -> t `SuchThat` c (c p q) r
  assocR :: t `SuchThat` c (c p q) r -> t `SuchThat` c p (c q r)

class Distributes c c' where
  distribute   :: t `SuchThat` c p (c' q r) -> t `SuchThat` c' (c p q) (c p r)
  undistribute :: t `SuchThat` c' (c p q) (c p r) -> t `SuchThat` c p (c' q r)
  
instance Commutative Or where
  commute = coerce

instance Commutative And where
  commute = coerce

instance Associative Or where
  assocL = coerce
  assocR = coerce

instance Associative And where
  assocL = coerce
  assocR = coerce

instance Distributes Or Or where
  distribute   = coerce
  undistribute = coerce

instance Distributes And And where
  distribute   = coerce
  undistribute = coerce

instance Distributes And Or where
  distribute   = coerce
  undistribute = coerce

instance Distributes Or And where
  distribute   = coerce
  undistribute = coerce

class NegatesTo c c' where
  negate' :: t `SuchThat` c -> t `SuchThat` c'

instance NegatesTo (Not (And p q)) (Or (Not p) (Not q)) where
  negate'   = coerce
  
instance NegatesTo (Or (Not p) (Not q)) (Not (And p q)) where
  negate'   = coerce

instance NegatesTo (Not (Or p q)) (And (Not p) (Not q)) where
  negate'   = coerce

instance NegatesTo (And (Not p) (Not q)) (Not (Or p q)) where
  negate'   = coerce

data ElementsSatisfy p

filter'' :: Fun f a Bool -> [a] `SuchThat` p -> [a] `SuchThat` And (ElementsSatisfy f) p
filter'' f xs = coerce (filter (apply f) (theValue xs))

newtype Fun f a b = Fun (a -> b)

apply :: Fun f a b -> a -> b
apply (Fun f) = f

withFunction :: (a -> b) -> (forall f. Fun f a b -> t) -> t
withFunction f k = k (coerce f)

data Even
data Odd

class Add p q where
  type family R p q :: *
  add :: Num n => n `SuchThat` p -> n `SuchThat` q -> n `SuchThat` (R p q)
  add (Value x) (Value y) = Value (x + y)
  
instance Add Even Even where
  type R Even Even = Even

instance Add Even Odd where
  type R Even Odd = Odd

instance Add Odd Even where
  type R Odd Even = Odd

instance Add Odd Odd where
  type R Odd Odd = Even

class Tautology p

tauto :: Tautology p => a -> a `SuchThat` p
tauto = coerce

instance Tautology (Even `Or` Odd)

class Decidable p n where
  decideBy :: n -> Bool

decide :: forall p n. Decidable p n => n -> Either (n `SuchThat` p) (n `SuchThat` Not p)
decide x = if decideBy @p x then Left (coerce x) else Right (coerce x)

instance Integral n => Decidable Even n where decideBy = even
instance Integral n => Decidable Odd  n where decideBy = odd

doubleBad :: forall n. Integral n => n -> n `SuchThat` Even
doubleBad x = case decide @Even x of
  Left  x' -> add x' x'
  Right x' -> let x'' = simplify x' in add x'' x''
  
{-
cases :: (a -> b) -> a `SuchThat` (p `Or` q) -> b
-- or_elim is faulty, what is a better formulation?!
double :: forall n. Num n => n -> n `SuchThat` Even
double x = or_elim (\y -> add y y) (\y -> add y y) (tauto x :: n `SuchThat` (Even `Or` Odd))
-}

-- `SuchThat` allows us to put preconditions on arguments, and
-- postconditions on results. What about preconditions that are
-- formulated as predicates over several arguments at once?
data TRUE
data FALSE

class Simplifiable p p' | p -> p' where
  simplify :: t `SuchThat` p -> t `SuchThat` p'
  simplify = coerce
  
instance Simplifiable (And TRUE p) p where
  simplify = coerce

instance Simplifiable (And p TRUE) p where
  simplify = coerce

instance Simplifiable (And p FALSE) FALSE where
  simplify = coerce

instance Simplifiable (And FALSE p) FALSE where
  simplify = coerce

instance Simplifiable (Or TRUE p) TRUE where
  simplify = coerce

instance Simplifiable (Or p TRUE) TRUE where
  simplify = coerce

instance Simplifiable (Or FALSE p) p where
  simplify = coerce

instance Simplifiable (Or p FALSE) p where
  simplify = coerce

instance Simplifiable (Not (Not p)) p where
  simplify = coerce

instance Simplifiable (And p p) p where
  simplify = coerce

instance Simplifiable (Or p p) p where
  simplify = coerce

{- Can't add these! "Functional dependencies conflict between instance declarations"
instance Simplifiable (And p (Not p)) FALSE where
  simplify = coerce

instance Simplifiable (And (Not p) p) FALSE where
  simplify = coerce

instance Simplifiable (Or p (Not p)) TRUE where
  simplify = coerce

instance Simplifiable (Or (Not p) p) TRUE where
  simplify = coerce
-}

plain :: a -> a `SuchThat` TRUE
plain = coerce

data Neg f

neg :: Fun f a Bool -> Fun (Neg f) a Bool
neg (Fun f) = Fun (not . f)

negneg_elim :: Fun (Neg (Neg f)) a Bool -> Fun f a Bool
negneg_elim = coerce

negneg_intro :: Fun f a Bool -> Fun (Neg (Neg f)) a Bool
negneg_intro = coerce

-- Sorted lists

newtype OList phi a = OList [a]

theList :: OList phi a -> [a]
theList (OList xs) = xs

newtype Comp phi a = Comp { comp :: a -> a -> Ordering }

withComparator :: forall a t.
     (a -> a -> Ordering)
  -> (forall phi. Given (Comp phi a) => Proxy phi -> t)
  -> t
withComparator comp k = reify comp body
  where
    body :: forall phi'. Reifies phi' (a -> a -> Ordering) => Proxy phi' -> t
    body = \_ -> give @(Comp phi' a) (coerce comp) (k @phi' $ Proxy) 

sortBy :: Comp phi a -> [a] -> OList phi a
sortBy (Comp c) = OList . L.sortBy c

sort :: Given (Comp phi a) => [a] -> OList phi a
sort = sortBy given

merge :: forall phi a. Given (Comp phi a) => OList phi a -> OList phi a -> OList phi a
merge (OList xl) (OList yl) = OList (go xl yl)
  where
    Comp comp = given :: Comp phi a
    go xs ys = case (xs, ys) of
      ([], _) -> ys
      (_, []) -> xs
      ((x:xs'), (y:ys')) -> if  x `comp` y == GT
                           then y : go xs  ys'
                           else x : go xs' ys
                        
  
instance Simplifiable (Not Even) Odd
instance Simplifiable (Not Odd) Even


class Known p where
  known :: Proof p

length :: (a ::: Length n) -> Proof n

type_Length_arg :: Length n -> Proof (n ∈ Nat)

induction :: (Proof (p Z)) -> ((n == S n' /\ p n') -> Proof (p n)) -> Proof (ForAll' Nat p)
                                               
length_cases :: (Known (n == Z) => t)
             -> (Known (n == S n') => a -> ([a] ::: Length n') -> t)
             -> ([a] ::: Length n)
             -> t

cons_Length :: a -> ([a] ::: Length n) -> ([a] ::: Length (S n))
cons_Length x xs = assert (x:xs)

map' :: (a -> b) -> ([a] ::: Length n) -> ([b] ::: Length n)
map' f xs' = length_cases xs' nil_case cons_case
  where
    nil_case = xs'
    cons_case x xs = cons_Length (f x) (map' f xs) -- ::: Length (S n')
    
(++) :: ([a] ::: Length x) -> ([a] ::: Length y) -> ([a] ::: Length (x + y))
