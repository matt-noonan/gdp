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
  , (++)

  , replicate
  , take
  , drop
  ) where

import Prelude hiding (head, tail, length, (++), replicate, take, drop, succ, cons)

import Logic.Propositional
import Theory.Lists.Assumed

import Theory.Nat
import Tactics

import GHC.TypeLits (Nat)

newtype Length xs = Length Defn

instance Argument (Length xs) 0 where
  type GetArg (Length xs) 0     = xs
  type SetArg (Length xs) 0 xs' = Length xs'

length :: forall xs a. ([a] ~~ xs)
      -> (Integer ~~ Length xs :::
             (IsNil  xs --> Length xs == Zero)
           && (IsCons xs --> Length xs == Succ (Length (Tail xs))))

length = toDefDisj $ list_cases
    (\_      -> zero)
    (\_ _ xs -> succ $. length xs)

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
            ::: (IsNil  xs --> (xs ++ ys) == ys)
             && (IsCons xs --> (xs ++ ys) == Cons (Head xs) (Tail xs ++ ys) ))

(++) xs ys = toDefDisj
  (list_cases
    (\_       -> ys)
    (\_ x xs' -> cons x (the $ xs' ++ ys)))
  xs

newtype Take n xs = Take Defn

instance Argument (Take n xs) 0 where
  type GetArg (Take n xs) 0    = n
  type SetArg (Take n xs) 0 n' = Take n' xs

instance Argument (Take n xs) 1 where
  type GetArg (Take n xs) 1     = xs
  type SetArg (Take n xs) 1 xs' = Take n xs'

take :: (Integer ~~ n)
    -> ([a] ~~ xs)
    -> ([a] ~~ Take n xs
            ::: (IsNil xs --> Take n xs == xs)
            && (IsCons xs --> ( (IsZero n --> Take n xs == xs)
                            && (IsSucc n --> Take n xs == Cons (Head xs) (Take (Pred n) (Tail xs))) )) )

take n xs = toDefDisj
  (list_cases 
    (\_ -> xs)
    (\_ hd tl -> nat_cases'
                  (\_ -> xs)
                  (\_ p -> cons hd $. take p tl)
                  n)
  ) xs


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
            ::: (IsNil xs --> Drop n xs == xs)
            && (IsCons xs --> ( (IsZero n --> Drop n xs == xs)
                            && (IsSucc n --> Drop n xs == Drop (Pred n) (Tail xs)) )) )
drop n xs = toDefDisj
  (list_cases
    (\_ -> xs)
    (\_ _ tl -> nat_cases'
                   (\_ -> xs)
                   (\_ p -> the (drop p tl))
                   n)
  ) xs

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
                 ::: (IsZero n --> Replicate n x == Nil)
                  && (IsSucc n --> Replicate n x == Cons x (Replicate (Pred n) x)))
replicate n x = toDefDisj (nat_cases'
  (\_    -> nil)
  (\_ n' -> cons x $. replicate n' x))
  n

impl_match :: MatchCtor p => (p --> q) -> Proof q
impl_match impl = match_ctor |$ modus_ponens impl

lemma_replicate_length :: forall n x. Proof (Length (Replicate n x) == n)
lemma_replicate_length =  toSpec replicate
                       |$ discrim
                       |. or_elim zeroC succC
  where
    
    zeroC  :: (IsZero n && Replicate n x == Nil) -> Proof (Length (Replicate n x) == n)
    zeroC conj = do
      (z, eq)     <- and_elim conj
      zero_is_n   <- zero_case z symmetric
      len_nil_is_zero <- length_of_nil_is_zero
      apply (arg @0) eq |$ transitive' len_nil_is_zero
                        |. transitive' zero_is_n

    length_cons_is_succ :: forall a as. Proof (Length (Cons a as) == Succ (Length as))
    length_cons_is_succ =  do
      c   <- toSpec length |$ and_elimR |. impl_match
      tail_of_cons |$ apply (arg @0) |. apply (arg @0) |. transitive c

    succC :: (IsSucc n && Replicate n x == Cons x (Replicate (Pred n) x)) -> Proof (Length (Replicate n x) == n)
    succC conj = do
      (s, eq) <- and_elim conj
      lcs     <- length_cons_is_succ
      rlen    <- lemma_replicate_length -- danger, danger !!
      
      eq1 <- apply (arg @0) eq
      eq2 <- apply (arg @0) rlen
      sp <- succ_pred_lemma
      x <- transitive eq1 lcs
      y <- transitive x eq2
      transitive y sp

length_of_nil_is_zero :: Proof (Length Nil == Zero)
length_of_nil_is_zero = do
  noncons <- nil_isn't_cons
  do  toSpec length
   |$ discrim
   |. or_elimL and_elimR
   |/ and_elimL
   |. contradicts' noncons
   |. absurd

length_of_cons_is_succ :: forall x xs. Proof (Length (Cons x xs) == Succ (Length xs))
length_of_cons_is_succ = do
  ic <- iscons
  ls <- toSpec length |$ and_elimR |. impl_elim ic :: Proof (Length (Cons x xs) == Succ (Length (Tail (Cons x xs))))
  toc <- tail_of_cons |$ apply (arg @0) |. apply (arg @0)
  transitive ls toc
  
nonzero_length_implies_cons :: (Length xs == Succ n) -> Proof (IsCons xs)
nonzero_length_implies_cons eq =
  do  toSpec length
   |$ discrim
   |. or_elimR and_elimL
   |/ and_elimR
   |. symmetric
   |. transitive' eq
   |. (contradicts' $$ zero_not_succ)
   |. absurd

length_sum_lemma
  :: forall xs ys. Proof (Length (xs ++ ys) == Length xs + Length ys)

length_sum_lemma =  toSpec (++)
                 |$ discrim
                 |. or_elim nilC consC
  where
    nilC :: (IsNil xs && (xs ++ ys) == ys) -> Proof (Length (xs ++ ys) == Length xs + Length ys)
    nilC conj = do
      n     <- and_elimL conj
      lxss  <- and_elimR conj |$ apply (arg @0) :: Proof (Length (xs ++ ys) == Length ys)
      lxss' <- zero_neutralL |$ transitive lxss :: Proof (Length (xs ++ ys) == Zero + Length ys)
      zln   <- (length_of_nil_is_zero |$ symmetric) :: Proof (Zero == Length Nil)
      nxs   <- (nil_unique n |$ symmetric |. apply (arg @0)) :: Proof (Length Nil == Length xs)
      eq    <- transitive zln nxs
      eq'   <- apply (arg @0) eq
      transitive lxss' eq'

    consC :: forall xs ys. (IsCons xs && (xs ++ ys) == Cons (Head xs) (Tail xs ++ ys)) -> Proof (Length (xs ++ ys) == Length xs + Length ys)
    consC conj = do
      c    <- and_elimL conj
      lxss <- and_elimR conj |$ apply (arg @0) :: Proof (Length (xs ++ ys) == Length (Cons (Head xs) (Tail xs ++ ys)))
      lcs  <- length_of_cons_is_succ
      eq   <- transitive lxss lcs :: Proof (Length (xs ++ ys) == Succ (Length (Tail xs ++ ys)))
      sal  <- succ_addL
      ind  <- length_sum_lemma |$ apply (arg @0) |. transitive' sal :: Proof (Succ (Length (Tail xs ++ ys)) == Succ (Length (Tail xs)) + Length ys)
      ls   <- lcons |$ symmetric |. apply (arg @0) :: Proof (Succ (Length (Tail xs)) + Length ys == Length (Cons (Head xs) (Tail xs)) + Length ys)
      csh  <- list_shape_lemma |$ undiscrim |. and_elimR |. impl_elim c |. symmetric |. apply (arg @0) |. apply (arg @0)
      transitive eq ind |$ transitive' ls |. transitive' csh
      
      

    succ_addL :: forall n m. Proof (Succ (n + m) == Succ n + m)
    succ_addL = do
      ca  <- commutative
      p   <- succ_add |$ symmetric |. transitive' ca :: Proof (Succ (m + n) == Succ n + m)
      ca' <- commutative |$ apply (arg @0)
      transitive ca' p
      

    lcons :: forall h t. Proof (Length (Cons h t) == Succ (Length t))
    lcons = do
      ls <- toSpec length |$ and_elimR |. impl_match  :: Proof (Length (Cons h t) == Succ (Length (Tail (Cons h t))))
      toc <- tail_of_cons |$ apply (arg @0) |. apply (arg @0)
      transitive ls toc

newtype Index xs n = Index Defn


index :: forall a xs n.
         ([a] ~~ xs)
      -> (Integer ~~ n ::: n < Length xs)
      -> (a ~~ Index xs n ::: ( (IsZero n --> Index xs n == Head xs)
                            && (IsSucc n --> Index xs n == Index (Tail xs) (Pred n)) ))
index xs n = toDefDisj (nat_cases'
    (\_ -> head (inject nonempty xs))
    (\is pn -> the $ index (tail (inject nonempty xs)) (inject (tailpred is) pn)))
    (the n)
  where
    nonzero_length :: Proof (Zero < Length xs)
    nonzero_length = do
      np <- getProp n
      zero_min |$ or_elim (\e -> substitute (arg @0) e np) (transitive' np)
    
    nonempty :: Proof (IsCons xs)
    nonempty = do
      zll <- nonzero_length |$ separated :: Proof (Zero /= Length xs)
      ns <- do  nat_classify
             |$ discrim
             |. or_elimR and_elimR
             |/ and_elimR
             |. symmetric
             |. contradicts' zll
             |. absurd               -- Proof (Length xs == Succ (Pred (Length xs)))
      nonzero_length_implies_cons ns
      
    tailpred :: Proof (IsSucc n) -> Proof (Pred n < Length (Tail xs))
    tailpred pis = do
      is <- pis
      nsp <- nat_classify |$ and_elimR |. impl_elim is :: Proof (n == Succ (Pred n))
      ieq <- getProp n |$ substitute (arg @0) nsp :: Proof (Succ (Pred n) < Length xs)
      ne <- nonempty
      lp <- toSpec length |$ and_elimR |. impl_elim ne :: Proof (Length xs == Succ (Length (Tail xs)))
      substitute (arg @1) lp ieq |$ order_pred

{-
leftPad :: Integer -> a -> [a] -> [a]
leftPad n x xs =
  naming n $ \n' ->
    naming x $ \x' ->
      naming xs' $ \xs' -> bare $ leftPad' n' x' xs'

type LeftPad n x xs = Replicate (n `Natsub` Length xs) x ++ xs
leftPad' :: (Integer ~~ n)
        -> (a ~~ x)
        -> ([a] ~~ xs)
        -> ([a] ~~ LeftPad n x xs)

leftPad' n x xs = replicate (n `natsub` length xs) x ++ xs

type Hillel_leftPad_spec_pt1 n x xs k
  = Not (n > Length xs) -> Proof (Index k xs == Index k (LeftPad n x xs))

type Hillel_leftPad_spec_pt2 n x xs k
  = (n < Length xs) -> (k < (n `Natsub` Length xs)) -> Proof (Index k (LeftPad n x xs) == x)

type Hillel_leftPad_spec_pt3 n x xs k
  = (n < Length xs) -> Not (k < (n `Natsub` Length xs)) -> Proof (Index k (LeftPad n x xs) == Index (k + (n `Natsub` Length xs)) xs)

  
natsub :: (Integer ~~ x)
       -> (Integer ~~ y)
       -> (Integer ~~ Natsub x y ::: ((y < x) && (y + Natsub x y == x)) || (Not (y < x) && Natsub x y == Zero))
natsub x y = error "todo"
-}
