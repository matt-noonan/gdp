{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Theory.Lists
    ( -- * Basic functions on lists
      head, tail, cons, nil
      -- ** Names for parts of a list
    , Head, Tail
      -- ** Names for basic list operations
    , Cons', Nil'
      -- * Reasoning about lists
      -- ** Predicates about list shapes
    , IsList, IsCons, IsNil
      -- ** Axioms about list shapes
    , consIsList, nilIsList, listIsList
    , listShapes, consIsCons, headOfCons, tailOfCons
      -- ** Induction principle
    , listInduction
      -- * Pattern-matching on lists
      -- ** Decompositions that use explicit evidence-passing
    , classify, ListCase (..)
      -- *** Pattern synonyms
    , pattern IsCons, pattern IsNil
      -- ** Decompositions that use implicit evidence-passing
    , classify', ListCase' (..)
      -- *** Pattern synonyms
    , pattern Cons, pattern Nil
    ) where

import           Prelude             hiding (cons, head, reverse, tail)
import qualified Prelude

import           Data.The
import           Logic.Implicit
import           Logic.Proof
import           Logic.Propositional
import           Theory.Equality
import           Theory.Named

-- | Predicates about the possible shapes of lists.
data IsList xs
data IsCons xs
data IsNil  xs

-- | Names for the parts of a list.
newtype Head xs = Head Defn
newtype Tail xs = Tail Defn

-- | Possible shapes of a list, along with evidence that the list
--   has the given shape.
data ListCase a xs
  = IsCons_ (Proof (IsCons xs)) (a ~~ Head xs) ([a] ~~ Tail xs)
  | IsNil_  (Proof (IsNil  xs))

-- | Classify a named list by shape, producing evidence that the
--   list matches the corresponding case.
classify :: ([a] ~~ xs) -> ListCase a xs
classify xs = case the xs of
    (h:t) -> IsCons_ axiom (defn h) (defn t)
    []    -> IsNil_  axiom

pattern IsCons :: Proof (IsCons xs) -> (a ~~ Head xs) -> ([a] ~~ Tail xs) -> ([a] ~~ xs)
pattern IsCons proof hd tl <- (classify -> IsCons_ proof hd tl)

pattern IsNil :: Proof (IsNil xs) -> ([a] ~~ xs)
pattern IsNil proof <- (classify -> IsNil_ proof)

-- | A variation on @ListCase@ that passes the shape facts implicitly. Pattern-matching on a
--   constructor of @ListCase'@ will bring a shape proof into the implicit context.
data ListCase' a xs where
    Cons_ :: Fact (IsCons xs) => (a ~~ Head xs) -> ([a] ~~ Tail xs) -> ListCase' a xs
    Nil_  :: Fact (IsNil  xs) => ListCase' a xs

-- | Classify a named list by shape, producing /implicit/ evidence that the
--   list matches the corresponding case.
classify' :: forall a xs. ([a] ~~ xs) -> ListCase' a xs
classify' xs = case the xs of
    (h:t) -> note (axiom :: Proof (IsCons xs)) (Cons_ (defn h) (defn t))
    []    -> note (axiom :: Proof (IsNil  xs))  Nil_

pattern Cons :: () => Fact (IsCons xs) => (a ~~ Head xs) -> ([a] ~~ Tail xs) -> ([a] ~~ xs)
pattern Cons hd tl <- (classify' -> Cons_ hd tl)

pattern Nil :: () => Fact (IsNil xs) => ([a] ~~ xs)
pattern Nil <- (classify' -> Nil_)

-- | Extract the first element from a non-empty list.
head :: Fact (IsCons xs) => ([a] ~~ xs) -> (a ~~ Head xs)
head (The xs) = defn (Prelude.head xs)

-- | Extract all but the first element from a non-empty list.
tail :: Fact (IsCons xs) => ([a] ~~ xs) -> ([a] ~~ Tail xs)
tail (The xs) = defn (Prelude.tail xs)

-- | Construct a list from an element and another list.
cons :: (a ~~ x) -> ([a] ~~ xs) -> ([a] ~~ Cons' x xs)
cons (The x) (The xs) = defn (x:xs)

-- | The empty list, named @Nil'@.
nil :: ([a] ~~ Nil')
nil = defn []

-- | A name for referring to the result of a @cons@ operation.
newtype Cons' x xs = Cons' Defn

-- | A name for referring to the empty list.
newtype Nil' = Nil' Defn

-- | Axiom: The @head@ of @cons x y@ is @x@.
headOfCons :: Proof (Head (Cons' x xs) == x)
headOfCons = axiom

-- | Axiom: The @tail@ of @cons x y@ is @y@.
tailOfCons :: Proof (Tail (Cons' x xs) == xs)
tailOfCons = axiom

-- | Axiom: The result of @cons x y@ satisfies @IsCons@.
consIsCons :: Proof (IsCons (Cons' x xs))
consIsCons = axiom

-- | Axiom: The empty list satisfies @IsNil@.
nilIsNil :: Proof (IsNil Nil')
nilIsNil = axiom

-- | Axiom: a list @xs@ satisfies exactly one of @IsCons xs@ or @IsNil xs@.
listShapes :: Proof (IsList xs) -> Proof ( (IsNil xs && Not (IsCons xs)) || (IsCons xs && Not (IsNil xs)) )
listShapes _ = axiom

-- | Induction principle: If a predicate @P@ is true for the empty list, and
--   @P@ is true for a list whenever it is true for the tail of the list,
--   then @P@ is true.
listInduction :: Proof (IsList xs) -> Proof (p Nil') -> Proof (ForAll ys ((IsList ys && p (Tail ys)) --> p ys)) -> Proof (p xs)
listInduction _ _ _ = axiom

consIsList :: Proof (IsCons xs) -> Proof (IsList xs)
consIsList _ = axiom

nilIsList :: Proof (IsNil xs) -> Proof (IsList xs)
nilIsList _ = axiom

listIsList :: ([a] ~~ xs) -> Proof (IsList xs)
listIsList _ = axiom
