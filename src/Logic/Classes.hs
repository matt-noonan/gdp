{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}

{-|
  Module      :  Logic.Classes
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Logic.Classes
  ( -- * Algebraic properties
    Reflexive(..)
  , Symmetric(..)
  , Transitive(..)
  , transitive'

  , Idempotent(..)
  , Commutative(..)
  , Associative(..)
  , DistributiveL(..)
  , DistributiveR(..)

  , Injective(..)

  ) where

import Logic.Proof
import Theory.Equality

{--------------------------------------------------------
  Special properties of predicates and functions
--------------------------------------------------------}

{-| A binary relation R is /reflexive/ if, for all x,
    R(x, x) is true. The @Reflexive r@ typeclass provides
    a single method, @refl :: Proof (r x x)@,
    proving R(x, x) for an arbitrary x.

    Within the module where the relation @R@ is defined, you can
    declare @R@ to be reflexive with an empty instance:

@
-- Define a reflexive binary relation
data SameColor p q
instance Reflexive SameColor
@
-}
class Reflexive r where
  refl :: Proof (r x x)
  refl = axiom

{-| A binary relation R is /symmetric/ if, for all x and y,
    R(x, y) is true if and only if R(y, x) is true. The
    @Symmetric@ typeclass provides
    a single method, @symmetric :: r x y -> Proof (r y x)@,
    proving the implication "R(x, y) implies R(y, x)".

    Within the module where @R@ is defined, you can
    declare @R@ to be symmetric with an empty instance:

@
-- Define a symmetric binary relation
data NextTo p q
instance Symmetric NextTo
@
-}
class Symmetric c where
  symmetric :: Proof (c p q) -> Proof (c q p)
  symmetric _ = axiom

{-| A binary relation R is /transitive/ if, for all x, y, z,
    if R(x, y) is true and R(y, z) is true, then  R(x, z) is true.
    The @Transitive r@ typeclass provides
    a single method, @transitive :: r x y -> r y z -> Proof (r x z)@,
    proving R(x, z) from R(x, y) and R(y, z).

    Within the module where @R@ is defined, you can
    declare @R@ to be transitive with an empty instance:

@
-- Define a transitive binary relation
data CanReach p q
instance Transitive CanReach
@
-}
class Transitive c where
  transitive :: Proof (c p q) -> Proof (c q r) -> Proof (c p r)
  transitive _ _ = axiom

-- | @transitive@, with the arguments flipped.
transitive' :: Transitive c => Proof (c q r) -> Proof (c p q) -> Proof (c p r)
transitive' = flip transitive

{-| A binary operation @#@ is idempotent if @x # x == x@ for all @x@.
    The @Idempotent c@ typeclass provides a single method,
    @idempotent :: Proof (c p p == p)@.

    Within the module where @F@ is defined, you can declare @F@ to be
    idempotent with an empty instance:

@
-- Define an idempotent binary operation
data Union x y
instance Idempotent Union
@
-}
class Idempotent c where
  idempotent :: Proof (c p p == p)
  idempotent = axiom

{-| A binary operation @#@ is commutative if @x # y == y # x@ for all @x@ and @y@.
    The @Commutative c@ typeclass provides a single method,
    @commutative :: Proof (c x y == c y x)@.

    Within the module where @F@ is defined, you can declare @F@ to be
    commutative with an empty instance:

@
-- Define a commutative binary operation
data Union x y
instance Commutative Union
@
-}
class Commutative c where
  commutative :: Proof (c p q == c q p)
  commutative = axiom

{-| A binary operation @#@ is associative if @x # (y # z) == (x # y) # z@ for
    all @x@, @y@, and @z@.
    The @Associative c@ typeclass provides a single method,
    @associative :: Proof (c x (c y z) == c (c x y) z)@.

    Within the module where @F@ is defined, you can declare @F@ to be
    associative with an empty instance:

@
-- Define an associative binary operation
data Union x y
instance Associative Union
@
-}
class Associative c where
  associative :: Proof (c p (c q r) == c (c p q) r)
  associative = axiom

{-| A binary operation @#@ distributes over @%@ on the left if
    @x # (y % z) == (x # y) % (x # z)@ for
    all @x@, @y@, and @z@.
    The @DistributiveL c c'@ typeclass provides a single method,
    @distributiveL :: Proof (c x (c' y z) == c' (c x y) (c x z))@.

    Within the module where @F@ and @G@ are defined, you can declare @F@ to
    distribute over @G@ on the left with an empty instance:

@
-- x `Union` (y `Intersect` z) == (x `Union` y) `Intersect` (x `Union` z)
data Union     x y
data Intersect x y
instance DistributiveL Union Intersect
@
-}
class DistributiveL c c' where
  distributiveL :: Proof (c p (c' q r) == c' (c p q) (c p r))
  distributiveL = axiom

{-| A binary operation @#@ distributes over @%@ on the right if
    @(x % y) # z == (x # z) % (y # z)@ for
    all @x@, @y@, and @z@.
    The @DistributiveR c c'@ typeclass provides a single method,
    @distributiveR :: Proof (c (c' x y) z == c' (c x z) (c y z))@.

    Within the module where @F@ and @G@ are defined, you can declare @F@ to
    distribute over @G@ on the left with an empty instance:

@
-- (x `Intersect` y) `Union` z == (x `Union` z) `Intersect` (y `Union` z)
data Union     x y
data Intersect x y
instance DistributiveR Union Intersect
@
-}
class DistributiveR c c' where
  distributiveR :: Proof (c (c' p q) r == c' (c p r) (c q r))
  distributiveR = axiom

{-| A function @f@ is /injective/ if @f x == f y@ implies @x == y@.
    The @Injective f@ typeclass provides a single method,
    @elim_inj :: (f x == f y) -> Proof (x == y)@.

    Within the module where @F@ is defined, you can declare @F@ to be
    injective with an empty instance:

@
-- {x} == {y} implies x == y.
data Singleton x
instance Injective Singleton
@
-}
class Injective f where
  elim_inj :: Proof (f x == f y) -> Proof (x == y)
  elim_inj _ = axiom


{--------------------------------------------------------
  Properites of equality
--------------------------------------------------------}

instance Reflexive Equals where
  refl = axiom

instance Symmetric Equals where
  symmetric _ = axiom

instance Transitive Equals where
  transitive _ _ = axiom
