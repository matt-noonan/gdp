{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}

{-|
  Module      :  Logic.NegClasses
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Logic.NegClasses
  ( -- * Algebraic properties
    Irreflexive(..)
  , Antisymmetric(..)
  ) where

import Logic.Proof
import Logic.Propositional (Not)

{--------------------------------------------------------
  Special properties of predicates and functions
--------------------------------------------------------}

{-| A binary relation R is /irreflexive/ if, for all x,
    R(x, x) is false. The @Irreflexive r@ typeclass provides
    a single method, @irrefl :: Proof (Not (r x x))@,
    proving the negation of R(x, x) for an arbitrary x.

    Within the module where the relation @R@ is defined, you can
    declare @R@ to be irreflexive with an empty instance:

@
-- Define an irreflexive binary relation
newtype DifferentColor p q = DifferentColor Defn
instance Irreflexive DifferentColor
@
-}
class Irreflexive r where
  irrefl :: Proof (Not (r x x))
  irrefl = axiom


{-| A binary relation R is /antisymmetric/ if, for all x and y,
    when R(x, y) is true, then R(y, x) is false. The
    @Antisymmetric@ typeclass provides
    a single method, @antisymmetric :: r x y -> Proof (Not (r y x))@,
    proving the implication "R(x, y) implies the negation of R(y, x)".

    Within the module where @R@ is defined, you can
    declare @R@ to be antisymmetric with an empty instance:

@
-- Define an antisymmetric binary relation
newtype AncestorOf p q = AncestorOf Defn
instance Antisymmetric AncestorOf
@
-}
class Antisymmetric c where
  antisymmetric :: Proof (c p q) -> Proof (Not (c q p))
  antisymmetric _ = axiom
