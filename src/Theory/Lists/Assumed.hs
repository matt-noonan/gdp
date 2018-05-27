{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE DataKinds             #-}

module Theory.Lists.Assumed
  ( Nil
  , Cons
  , Head
  , Tail
  , IsNil
  , IsCons

  , head
  , tail
  
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

  , IsList
  , is_list
  , list_induction
  , tail_of_cons
  , iscons
  , nil_unique
  
  ) where

import Prelude hiding (head, tail)

import Logic.Propositional
import Theory.Nat
import Tactics

import Data.Proxy

newtype Nil       = Nil  Defn
newtype Cons x xs = Cons Defn
newtype Head xs   = Head Defn
newtype Tail xs   = Tail Defn

newtype IsNil  xs = IsNil  Defn
newtype IsCons xs = IsCons Defn

instance Argument (Tail xs) 0 where
  type GetArg (Tail xs) 0     = xs
  type SetArg (Tail xs) 0 xs' = Tail xs'

instance Argument (Head xs) 0 where
  type GetArg (Head xs) 0     = xs
  type SetArg (Head xs) 0 xs' = Head xs'

instance Argument (Cons x xs) 0 where
  type GetArg (Cons x xs) 0    = x
  type SetArg (Cons x xs) 0 x' = Cons x' xs

instance Argument (Cons x xs) 1 where
  type GetArg (Cons x xs) 1     = xs
  type SetArg (Cons x xs) 1 xs' = Cons x xs'
  

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

list_cases :: forall a xs t1 t2 t m1 m2. (ToMatch t1 t m1, ToMatch t2 t m2)
  => (Proof (IsNil xs) -> t1)
  -> (Proof (IsCons xs) -> (a ~~ Head xs) -> ([a] ~~ Tail xs) -> t2)
  -> ([a] ~~ xs)
  -> Match (MCons (MGuard (IsNil xs) m1)
                  (MGuard (IsCons xs) m2)) t
             
list_cases nilcase conscase
  = closeCases
  $   defCase' (Proxy @(IsNil xs)) ((\case { [] -> True; _ -> False}) . nameless) (const $ nilcase sorry)
  <++> defCase' (Proxy @(IsCons xs)) ((\case { [] -> False; _ -> True }) . nameless) (\xs -> let (h:t) = nameless xs in conscase sorry (assert_is h) (assert_is t))

{-
def_by_list_cases :: (Defining f, Argument f n, GetArg f n ~ xs)
         => Arg n
         -> (Proof (IsNil xs) -> (t ~~ nilcase))
         -> (Proof (IsCons xs) -> (a ~~ Head xs) -> ([a] ~~ Tail xs) -> (t ~~ conscase))
         -> ([a] ~~ xs) -> (t ~~ f ::: ((IsNil  xs && (f == nilcase))
                                       || (IsCons xs && (f == conscase))))

def_by_list_cases _ nilc consc xs = inject sorry $
  assert_is $ list_cases xs (nameless.nilc) (\p x xs -> nameless $ consc p x xs)
-}

list_def_impl :: ((IsNil xs && p) || (IsCons xs && q)) -> Proof ( (IsNil xs --> p) && (IsCons xs --> q) )
list_def_impl _ = sorry

newtype IsList xs = IsList Defn

is_list :: ([a] ~~ name) -> Proof (IsList name)
is_list _ = sorry

list_induction :: Proof (p Nil)                       -- ^ The nil case
         -> (forall x xs. p xs -> Proof (p (Cons x xs)))
         -> IsList ys -> Proof (p ys)
list_induction _ _ _ = sorry


instance Simplifiable (IsNil  Nil)         TRUE
instance Simplifiable (IsNil  (Cons x xs)) FALSE
instance Simplifiable (IsCons Nil)         FALSE
instance Simplifiable (IsCons (Cons x xs)) TRUE

head :: ([a] ~~ xs ::: IsCons xs) -> (a ~~ Head xs)
head xs = case bare xs of (h:_) -> assert_is h

tail :: ([a] ~~ xs ::: IsCons xs) -> ([a] ~~ Tail xs)
tail xs = case bare xs of (_:t) -> assert_is t

instance Discriminable ((IsNil xs --> p) && (IsCons xs --> q)) ((IsNil xs && p) || (IsCons xs && q)) where
  discrim   _ = sorry
  undiscrim _ = sorry

instance Selectable (IsNil xs) ((IsNil xs --> p) && (IsCons xs --> q)) p where
  select _ _ = sorry

instance SelectCase ((IsNil Nil --> p) && (IsCons Nil --> q)) p where
  select_case _ = sorry

instance Selectable (IsCons xs) ((IsNil xs --> p) && (IsCons xs --> q)) q where
  select _ _ = sorry

instance SelectCase ((IsNil (Cons x xs) --> p) && (IsCons (Cons x xs) --> q)) q where
  select_case _ = sorry

instance SelectCase ((IsNil (Cons x xs) && p) || (IsCons (Cons x xs) && q)) q where
  select_case _ = sorry

tail_of_cons :: Proof (Tail (Cons x xs) == xs)
tail_of_cons = sorry

iscons :: Proof (IsCons (Cons x xs))
iscons = sorry

instance MatchCtor (IsCons (Cons x xs))
instance MatchCtor (IsNil Nil)

nil_unique :: IsNil xs -> Proof (xs == Nil)
nil_unique _ = sorry

