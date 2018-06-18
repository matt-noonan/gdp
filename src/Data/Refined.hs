{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE FlexibleContexts      #-}

{-|
  Module      :  Data.Refined
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Data.Refined
  (  -- * Refinement types
    -- ** Attaching arbitrary propositions to values
    (:::)
  , (...)
  , (...>)
  , ($:)
  , exorcise
  , conjure

  -- ** Refinement types
  , Satisfies
  , type (?)
  , assert

  -- *** Forgetting and re-introducing names
  , unname
  , rename
  , (...?)

  -- *** Traversals over collections of refined types
  , traverseP, traverseP_
  , forP, forP_
  ) where

import Data.The
import Logic.Proof (Proof, axiom)
import Theory.Named

import Data.Coerce
import Data.Foldable (traverse_)

{--------------------------------------------------
  Attaching proofs to values
--------------------------------------------------}

{-| Given a type @a@ and a proposition @p@, the
    type @(a ::: p)@ represents a value of type @a@,
    with an attached "ghost proof" of @p@.

    Values of the type @(a ::: p)@ have
    the same run-time representation as values of
    the normal type @a@; the proposition @p@ does
    not carry a run-time space or time cost.
-}
newtype a ::: p = SuchThat a
infixr 1 :::

instance The a' a => The (a' ::: p) a where
  the (SuchThat x) = the x

-- | Given a value and a proof, attach the proof as a
--   ghost proof on the value.
(...) :: a -> Proof p -> (a ::: p)
x ...proof = coerce x

-- | Given a value and a proof, apply a function to the value
--   but leave the proof unchanged.
($:) :: (a -> b) -> (a ::: p) -> (b ::: p)
f $: x = coerce (f (exorcise x))

-- | Apply an implication to the ghost proof attached to a value,
--   leaving the value unchanged.
(...>) :: (a ::: p) -> (p -> Proof q) -> (a ::: q)
x ...> _ = coerce x

-- | Forget the ghost proof attached to a value.
exorcise :: (a ::: p) -> a
exorcise = coerce

-- | Extract the ghost proof from a value.
conjure :: (a ::: p) -> Proof p
conjure _ = axiom

{--------------------------------------------------
  Refinement types
--------------------------------------------------}

{-| Given a type @a@ and a predicate @p@, the type
    @a ?p@ represents a /refinement type/ for @a@.
    Values of type @a ?p@ should be values of type @a@
    that satisfy the predicate @p@.

    Values of type @a ?p@ have the same run-time representation
    as values of type @a@; the proposition @p@ does not carry a
    run-time space or time cost.
-}
newtype Satisfies (p :: * -> *) a = Satisfies a
instance The (Satisfies p a) a

-- | An infix alias for 'Satisfies'.
type a ?p = Satisfies p a
infixr 1 ?

-- | For library authors: assert that a property holds.
assert :: Defining (p ()) => a -> (a ?p)
assert x = name x (\x -> unname (x ...axiom))

-- | Existential introduction for names: given a named value of
--   type @a@ that satisfies a predicate @p@, coerce to a value
--   of type @a ?p@.
unname :: (a ~~ name ::: p name) -> (a ?p)
unname = coerce . the

-- | Existential elimination for names: given a value of type
--   @a ?p@, re-introduce a new name to produce a value of type
--   @a ~~ name ::: p name@.
rename :: (a ?p) -> (forall name. (a ~~ name ::: p name) -> t) -> t
rename x k = name (the x) (\x -> k (x ...axiom))

{-| Take a simple function with one named argument and a named return,
    plus an implication relating a precondition to a postcondition of the
    function, and produce a function between refined input and output types.

@
newtype NonEmpty xs = NonEmpty Defn
newtype Reverse  xs = Reverse  Defn

rev :: ([a] ~~ xs) -> ([a] ~~ Reverse xs)
rev xs = defn (reverse (the xs))

rev_nonempty_lemma :: NonEmpty xs -> Proof (NonEmpty (Reverse xs))

rev' :: ([a] ?NonEmpty) -> ([a] ?NonEmpty)
rev' = rev ...? rev_nonempty_lemma
@
-}

(...?) :: (forall name. (a ~~ name) -> (b ~~ f name))
      -> (forall name. p name -> Proof (q (f name)))
      -> (a ?p) -> (b ?q)
(...?) f _ x = rename x (\x -> unname (f (exorcise x) ...axiom))

-- | Traverse a collection of refined values, re-introducing names
--   in the body of the action.
traverseP :: (Traversable t, Applicative f)
          => (forall name. (a ~~ name ::: p name) -> f b)
          -> t (a ?p)
          -> f (t b)
traverseP f = traverse (\x -> rename x f)

-- | Same as 'traverseP', but ignores the action's return value.
traverseP_ :: (Foldable t, Applicative f)
          => (forall name. (a ~~ name ::: p name) -> f b)
          -> t (a ?p)
          -> f ()
traverseP_ f = traverse_ (\x -> rename x f)

-- | Same as 'traverse', with the argument order flipped.
forP :: (Traversable t, Applicative f)
      => t (a ?p)
      -> (forall name. (a ~~ name ::: p name) -> f b)
      -> f (t b)
forP x f = traverseP f x

-- | Same as 'traverse_', with the argument order flipped.
forP_ :: (Foldable t, Applicative f)
      => t (a ?p)
      -> (forall name. (a ~~ name ::: p name) -> f b)
      -> f ()
forP_ x f = traverseP_ f x
