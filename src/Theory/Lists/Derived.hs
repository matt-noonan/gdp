{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}

module Theory.Lists.Derived
  ( head
  , tail

  , Length
  , length
  -- , (++)
{-
  , replicate
  , take
  , drop
-}
  ) where

import Prelude hiding (head, tail, length, (++), replicate, take, drop, succ, cons)

import Logic.Propositional
import Theory.Lists.Assumed

import Theory.Nat

import GHC.TypeLits (Nat)


head :: ([a] ~~ xs ::: IsCons xs) -> (a ~~ Head xs)
head xs = list_cases (the xs)
    -- Nil case
    (\is_nil -> impossible $ xs `by` cannot is_nil)
    -- Cons case
    (\_ x _ -> x)

  where
    cannot :: forall xs. Proof (IsNil xs) -> IsCons xs -> Proof FALSE
    cannot pn c = do
      n  <- pn
      conj <- and_intro c c
      disj <- or_introR conj :: Proof ((IsNil xs && Not (IsCons xs)) || (IsCons xs && IsCons xs))
      c' <- cases n disj
      contradicts c c'
        
tail :: ([a] ~~ xs ::: IsCons xs) -> ([a] ~~ Tail xs)
tail xs = list_cases (the xs)
    -- Nil case
    (\is_nil -> impossible $ xs `by` cannot is_nil)
    -- Cons case
    (\_ _ xs -> xs)

  where
    cannot :: forall xs. Proof (IsNil xs) -> IsCons xs -> Proof FALSE
    cannot pn c = do
      n  <- pn
      conj <- and_intro c c --  :: Proof (IsCons xs && IsCons xs)
      disj <- or_introR conj  :: Proof ((IsNil xs && Not (IsCons xs)) || (IsCons xs && IsCons xs))
      c' <- cases n disj
      contradicts c c'


newtype Length xs = Length Defn

instance Argument (Length xs) 0 where
  type GetArg (Length xs) 0     = xs
  type SetArg (Length xs) 0 xs' = Length xs'

length :: forall xs a. ([a] ~~ xs)
      -> (Integer ~~ Length xs :::
             (IsNil  xs && Length xs == Zero)
           || (IsCons xs && Length xs == Succ (Length (Tail xs))))

length = def_by_list_cases (arg @0)
  (\_      -> zero)
  (\_ _ xs -> succ $ the $ length xs)
  
newtype (++) xs ys = Append Defn
infixr 5 ++

instance Argument (xs ++ ys) 0 where
  type GetArg (xs ++ ys) 0     = xs
  type SetArg (xs ++ ys) 0 xs' = xs' ++ ys

instance Argument (xs ++ ys) 1 where
  type GetArg (xs ++ ys) 1     = ys
  type SetArg (xs ++ ys) 1 ys' = xs ++ ys'
  
(++) :: ([a] ~~ xs)
    -> ([a] ~~ ys)
    -> ([a] ~~ (xs ++ ys)
            ::: (IsNil  xs && (xs ++ ys) == ys)
             || (IsCons xs && (xs ++ ys) == Cons (Head xs) (Tail xs ++ ys) ))

(++) xs ys = def_by_list_cases (arg @0)
  (\_       -> ys)
  (\_ x xs' -> cons x (the $ xs' ++ ys))
  xs
         
newtype Take n xs = Take Defn

instance Argument (Take n xs) 0 where
  type GetArg (Take n xs) 0    = n
  type SetArg (Take n xs) 0 n' = Take n' xs

instance Argument (Take n xs) 1 where
  type GetArg (Take n xs) 1     = xs
  type SetArg (Take n xs) 1 xs' = Take n xs'

{-
take :: Integer -> [a] -> [a]
take n xs = case xs of
  [] -> []
  (hd:tl) -> case n of
              0 -> xs
              _ -> hd : take (n - 1) xs
-}

take :: (Integer ~~ n)
    -> ([a] ~~ xs)
    -> ([a] ~~ Take n xs
            ::: (IsNil xs && Take n xs == xs)
            || (IsCons xs && ( (IsZero n && Take n xs == xs)
                            || (IsSucc n && Take n xs == Cons x (Take (Pred n) (Tail xs))) )) )
take n xs = error "todo" {-def_by_list_cases (arg @1)
  (\_ -> xs)
  (\_ hd tl -> error "todo")
  xs
-}

newtype Drop n xs = Drop Defn

instance Argument (Drop n xs) 0 where
  type GetArg (Drop n xs) 0    = n
  type SetArg (Drop n xs) 0 n' = Drop n' xs

instance Argument (Drop n xs) 1 where
  type GetArg (Drop n xs) 1     = xs
  type SetArg (Drop n xs) 1 xs' = Drop n xs'

drop :: (Integer ~~ n)
    -> ([a] ~~ xs)
    -> ([a] ~~ Drop n xs
            ::: (IsNil xs && Drop n xs == xs)
            || (IsCons xs && ( (IsZero n && Drop n xs == xs)
                            || (IsSucc n && Drop n xs == Drop (Pred n) (Tail xs)) )) )
drop n xs = error "todo" {-def_by_list_cases (arg @1)
  (\_ -> xs)
  (\_ hd tl -> error "todo")
  xs
-}

{-
take n xs = def_by_list_cases (arg @1)
  (\_ -> xs)
  (\_ hd tl) -> inductP n (\nz -> inject z xs') (\nsp pn -> inject nsp (take pn xs')))
  xs
-}

newtype Replicate n x = Replicate Defn

instance Argument (Replicate n x) 0 where
  type GetArg (Replicate n x) 0    = n
  type SetArg (Replicate n x) 0 n' = Replicate n' x

instance Argument (Replicate n x) 1 where
  type GetArg (Replicate n x) 1    = x
  type SetArg (Replicate n x) 1 x' = Replicate n x'

replicate :: (Integer ~~ n)
         -> (a ~~ x)
         -> ([a] ~~ Replicate n x
                 ::: (IsZero n && Replicate n x == Nil)
                  || (IsSucc n && Replicate n x == Cons x (Replicate (Pred n) x)))
replicate n x = def_by_nat_cases (arg @0) n
  (\_    -> nil)
  (\_ n' -> cons x $. replicate n' x)

lemma_replicate_length :: forall n x. Proof (Length (Replicate n x) == n)
lemma_replicate_length =  toSpec replicate
                       |$ or_elim zeroC succC
  where
    
    zeroC  :: (IsZero n && Replicate n x == Nil) -> Proof (Length (Replicate n x) == n)
    zeroC conj = do
      (z, eq)     <- and_elim conj
      zero_is_n   <- zero_case z symmetric
      len_nil_is_zero <- length_of_nil_is_zero
      apply (arg @0) eq |$ transitive' len_nil_is_zero
                        |. transitive' zero_is_n
    
    succC :: (IsSucc n && Replicate n x == Cons x (Replicate (Pred n) x)) -> Proof (Length (Replicate n x) == n)
    succC conj = do
      (s, eq) <- and_elim conj
      --eq1 <- apply eq
      error "todo"

length_of_nil_is_zero :: Proof (Length Nil == Zero)
length_of_nil_is_zero = do
  noncons <- nil_isn't_cons
  do  toSpec length
   |$ or_elimL and_elimR
   |/ and_elimL
   |. contradicts' noncons
   |. absurd

nonzero_length_implies_cons :: (Length xs == Succ n) -> Proof (IsCons xs)
nonzero_length_implies_cons eq =
  do  toSpec length
   |$ or_elimR and_elimL
   |/ and_elimR
   |. symmetric
   |. transitive' eq
   |. (contradicts' $$ zero_not_succ)
   |. absurd

nac :: Proof (Not (IsCons Nil))
nac = not_intro $ \iscons -> do
  isnil <- nil_prop
  conj <- and_intro isnil iscons
  disj <- or_introL conj :: Proof ((IsNil Nil && IsCons Nil) || (IsCons Nil && FALSE))
  cases iscons disj
    
    --             (IsNil  xs && Length xs == Zero)
    --           || (IsCons xs && Length xs == Succ (Length (Tail xs))))

{-
tailAppend :: forall xs ys.
             Proof (Zero < Length xs || Zero < Length ys)
          -> ([a] ~~ xs)
          -> ([a] ~~ ys)
          -> ([a] ~~ Tail (xs ++ ys))

tailAppend proof xs ys = tail (xs ++ ys)
  where
    ap_len_sum :: Proof (Length (xs ++ ys) == Length xs + Length ys)

    append_pos_length :: Proof (Zero /= Length (xs ++ ys))
    append_pos_length = do  
      ap_spec <- toSpec (++)
      let xs_nil_case :: (Length xs == Zero) -> Proof (Append xs ys == ys)
          xs_nil_case 
    
(++) :: ([a] ~~ xs)
    -> ([a] ~~ ys)
    -> ([a] ~~ Append xs ys
            ::: (IsNil  xs && Append xs ys == ys)
             || (IsCons xs && Append xs ys == Cons (Head xs) (Append (Tail xs) ys)) )
      
length :: ([a] ~~ xs)
      -> (Integer ~~ Length xs :::
           (IsNil  xs && Length xs == Zero)
           || (IsCons xs && Length xs == Succ (Length (Tail xs))))
=-}

length_sum_lemma
  ::  IsList xs -> Proof (Length (xs ++ ys) == Length xs + Length ys)

length_sum_lemma xs_list = error "todo"
-- Length (Nil ++ ys) == Length Nil + Length ys
-- lhs : Length (Nil ++ ys) => Length ys => Zero + Length ys => Length Nil + Length ys
-- rhs : Length ys => Zero + Length ys => Length Nil + Length ys

-- (Length (xs ++ ys) == Length xs + Length ys) --> (Length (Cons x xs ++ ys) == Length (Cons x xs) + Length ys)

-- lhs : Length (Cons x xs ++ ys) => Length (Cons x (xs ++ ys)) => Succ (Length (xs ++ ys)) => Succ (Length xs + Length ys)
-- rhs : Length (Cons x xs) + Length ys => Succ (Length xs) + Length ys => Succ (Length xs + Length ys)

{-
flipAppend :: ([a] ~~ ys)
          -> ([a] ~~ xs)
          -> ([a] ~~ FlipAppend ys xs
            ::: (IsNil  xs && FlipAppend ys xs == ys)
             || (IsCons xs && FlipAppend ys xs == Cons (Head xs) (FlipAppend ys (Tail xs))) )
-}
