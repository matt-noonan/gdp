{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}

module Theory.Lists.Assumed
  ( Nil
  , Cons
  , Head
  , Tail
  , IsNil
  , IsCons

  , nil_prop
  , cons_prop
  
  , list_shape_lemma
  , nil_isn't_cons
  , cons_isn't_nil
  
  , cons
  , uncons
  , nil

  , list_cases
  , list_def_impl
  , def_by_list_cases
  , def_by_list_casesP

  , IsList
  , is_list
  , list_induction
  ) where

import Prelude hiding (head, tail)

import Logic.Propositional
import Theory.Nat

newtype Nil       = Nil  Defn
newtype Cons x xs = Cons Defn
newtype Head xs   = Head Defn
newtype Tail xs   = Tail Defn

newtype IsNil  xs = IsNil  Defn
newtype IsCons xs = IsCons Defn

list_shape_lemma :: Proof ( (IsNil xs && xs == Nil)
                         || (IsCons xs && xs == Cons (Head xs) (Tail xs)))
list_shape_lemma = sorry

nil_isn't_cons :: Proof (Not (IsCons Nil))
nil_isn't_cons = sorry

cons_isn't_nil :: Proof (Not (IsNil (Cons x xs)))
cons_isn't_nil = sorry

cons :: (a ~~ x) -> ([a] ~~ xs) -> ([a] ~~ Cons x xs)
cons = defining2' (:)

uncons :: ([a] ~~ Cons x xs) -> (a ~~ x, [a] ~~ xs)
uncons = decompose2 (\(x:xs) -> (x,xs))

nil :: [a] ~~ Nil
nil = assert_is []

nil_prop :: Proof (IsNil Nil)
nil_prop = sorry

cons_prop :: Proof (IsCons (Cons x xs))
cons_prop = sorry

list_cases :: ([a] ~~ xs)
          -> (Proof (IsNil xs) -> t)
          -> (Proof (IsCons xs) -> (a ~~ Head xs) -> ([a] ~~ Tail xs) -> t)
          -> t
list_cases lst nilcase conscase =
  case nameless lst of
    []     -> nilcase  sorry
    (x:xs) -> conscase sorry (assert_is x) (assert_is xs)

def_by_list_cases :: (Defining f, Argument f n, GetArg f n ~ xs)
         => Arg n
         -> (Proof (IsNil xs) -> (t ~~ nilcase))
         -> (Proof (IsCons xs) -> (a ~~ Head xs) -> ([a] ~~ Tail xs) -> (t ~~ conscase))
         -> ([a] ~~ xs) -> (t ~~ f ::: ((IsNil  xs && (f == nilcase))
                                       || (IsCons xs && (f == conscase))))

def_by_list_cases _ nilc consc xs = inject sorry $
  assert_is $ list_cases xs (nameless.nilc) (\p x xs -> nameless $ consc p x xs)

def_by_list_casesP :: (Defining f, Argument f n, GetArg f n ~ xs)
         => Arg n
         -> (Proof (IsNil xs) -> (t ~~ nilcase ::: p))
         -> (Proof (IsCons xs) -> (a ~~ Head xs) -> ([a] ~~ Tail xs) -> (t ~~ conscase ::: q))
         -> ([a] ~~ xs) -> (t ~~ f ::: ((IsNil  xs && (p && f == nilcase))
                                       || (IsCons xs && (q && f == conscase))))

def_by_list_casesP _ nilc consc xs = inject sorry $
  assert_is $ list_cases xs (bare.nilc) (\p x xs -> bare $ consc p x xs)

list_def_impl :: ((IsNil xs && p) || (IsCons xs && q)) -> Proof ( (IsNil xs --> p) && (IsCons xs --> q) )
list_def_impl _ = sorry

newtype IsList xs = IsList Defn

is_list :: ([a] ~~ name) -> Proof (IsList name)
is_list _ = sorry

list_induction :: Proof (p Nil)                       -- ^ The nil case
         -> (forall x xs. p xs -> Proof (p (Cons x xs)))
         -> IsList ys -> Proof (p ys)
list_induction _ _ _ = sorry


instance Cases (IsNil xs) ((IsNil xs && p) || (IsCons xs && q)) p where
  cases _ _ = sorry

instance Cases Nil ((IsNil Nil && p) || (IsCons Nil && q)) p where
  cases _ _ = sorry

instance Cases (IsCons xs) ((IsNil xs && p) || (IsCons xs && q)) q where
  cases _ _ = sorry

instance Cases (Cons x xs) ((IsNil (Cons x xs) && p) || (IsCons (Cons x xs) && q)) q where
  cases _ _ = sorry

