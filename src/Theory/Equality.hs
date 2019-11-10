{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RoleAnnotations       #-}

{-|
  Module      :  Theory.Equality
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Theory.Equality
  (
    Equals, type (==)

  -- ** Substitutions and equational reasoning
  , (==.)
  , apply
  , substitute
  , substituteL
  , substituteR

  -- ** Relating to other forms of equality
  , same
  , reflectEq
  , propEq
  ) where

import Data.Arguments
import Data.The
import Theory.Named
import Logic.Proof (Proof, axiom)

import Lawful

import Unsafe.Coerce
import Data.Type.Equality ((:~:)(..))

{--------------------------------------------------
  Theory of equality
--------------------------------------------------}

-- | The @Equals@ relation is used to express equality between two entities.
--   Given an equality, you are then able to substitute one side of the equality
--   for the other, anywhere you please.
newtype Equals x y = Equals Defn
type role Equals nominal nominal

-- | An infix alias for 'Equals'.
type x == y = x `Equals` y
infix 4 ==

instance Argument (Equals x y) 0 where
  type GetArg (Equals x y) 0    = x
  type SetArg (Equals x y) 0 x' = Equals x' y

instance Argument (Equals x y) 1 where
  type GetArg (Equals x y) 1    = y
  type SetArg (Equals x y) 1 y' = Equals x y'

instance Argument (Equals x y) LHS where
  type GetArg (Equals x y) LHS    = x
  type SetArg (Equals x y) LHS x' = Equals x' y

instance Argument (Equals x y) RHS where
  type GetArg (Equals x y) RHS    = y
  type SetArg (Equals x y) RHS y' = Equals x y'

-- | Chain equalities, a la Liquid Haskell.
(==.) :: Proof (x == y) -> Proof (y == z) -> Proof (x == z)
_ ==. _ = axiom

-- | Apply a function to both sides of an equality.
apply :: forall f n x x'. (Argument f n, GetArg f n ~ x)
    => Arg n -> Proof (x == x') -> Proof (f == SetArg f n x')
apply _ _ = axiom

-- | Given a formula and an equality over one of its arguments,
--   replace the left-hand side of the equality with the right-hand side.
substitute :: (Argument f n, GetArg f n ~ x)
    => Arg n -> Proof (x == x') -> f -> Proof (SetArg f n x')
substitute _ _ _ = axiom

-- | Substitute @x'@ for @x@ under the function @f@, on the left-hand side
--   of an equality.
substituteL :: (Argument f n, GetArg f n ~ x)
    => Arg n -> Proof (x == x') -> Proof (f == g) -> Proof (SetArg f n x' == g)
substituteL _ _ _ = axiom

-- | Substitute @x'@ for @x@ under the function @f@, on the right-hand side
--   of an equality.
substituteR :: (Argument f n, GetArg f n ~ x)
    => Arg n -> Proof (x == x') -> Proof (g == f) -> Proof (g == SetArg f n x')
substituteR _ _ _ = axiom

{--------------------------------------------------
  Theory of equality
--------------------------------------------------}

-- | Test if the two named arguments are equal and, if so, produce a proof
--   of equality for the names.
same :: Lawful Eq a => (a ~~ x) -> (a ~~ y) -> Maybe (Proof (x == y))
same (The x) (The y) = if x == y then Just axiom else Nothing

{-| Reflect an equality between @x@ and @y@ into a propositional
    equality between the /types/ @x@ and @y@.

@
newtype Bob = Bob Defn

bob :: Int ~~ Bob
bob = defn 42

needsBob :: (Int ~~ Bob) -> Int
needsBob x = the x + the x

isBob :: (Int ~~ name) -> Maybe (Proof (name == Bob))
isBob = same x bob

f :: (Int ~~ name) -> Int
f x = case reflectEq \<$\> isBob x of
  Nothing   -> 17
  Just Refl -> needsBob x x
@
-}
reflectEq :: Proof (x == y) -> (x :~: y)
reflectEq _ = unsafeCoerce (Refl :: a :~: a)

-- | Convert a propositional equality between the types @x@ and @y@
--   into a proof of @x == y@.
propEq :: (x :~: y) -> Proof (x == y)
propEq _ = axiom
