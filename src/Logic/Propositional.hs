{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-|
  Module      :  Logic.Propositional
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Logic.Propositional
  ( -- * First-order Logic

  -- ** Logical symbols
    TRUE, FALSE

  , And,     type (&&), type (∧), type (/\)
  , Or,      type (||), type (∨), type (\/)
  , Implies, type (-->)
  , Not
  , ForAll
  , Exists

  -- ** Natural deduction

  -- *** Tautologies
  , true
  , noncontra

  -- *** Introduction rules

  -- | Introduction rules give the elementary building blocks
  --   for creating a formula from simpler ones.
  , and_intro
  , and_intro'
  , or_introL
  , or_introR
  , impl_intro
  , not_intro
  , contrapositive
  , contradicts
  , contradicts'
  , univ_intro
  , ex_intro

  -- *** Elimination rules

  -- | Elimination rules give the elementary building blocks for
  --   decomposing a complex formula into simpler ones.
  , and_elimL
  , and_elimR
  , and_elim
  , or_elim
  , or_elimL
  , or_elimR
  , impl_elim
  , modus_ponens
  , modus_tollens
  , absurd
  , univ_elim
  , ex_elim

  -- *** Classical logic and the Law of the Excluded Middle
  , Classical
  , classically
  , lem
  , contradiction
  , not_not_elim

   -- *** Mapping over conjunctions and disjunctions
  , and_mapL
  , and_mapR
  , and_map

  , or_mapL
  , or_mapR
  , or_map

  , impl_mapL
  , impl_mapR
  , impl_map

  , not_map

  ) where

import Logic.Classes
import Logic.Proof
import Theory.Named

{--------------------------------------------------
  Logical constants
--------------------------------------------------}

-- | The constant "true".
newtype TRUE  = TRUE Defn

-- | The constant "false".
newtype FALSE = FALSE Defn

-- | The conjunction of @p@ and @q@.
newtype And p q = And Defn

-- | The disjunction of @p@ and @q@.
newtype Or p q  = Or  Defn

-- | The negation of @p@.
newtype Not p   = Not Defn

-- | The implication "@p@ implies @q@".
newtype Implies p q = Implies Defn

-- | Existential quantifiation.
newtype Exists x p = Exists Defn

-- | Universal quantification.
newtype ForAll x p = ForAll Defn

-- | An infix alias for @Or@.
type p || q   = p `Or` q

-- | An infix alias for @Or@.
type p ∨ q   = p `Or` q

-- | An infix alias for @Or@.
type p \/ q  = p `Or` q

-- | An infix alias for @And@.
type p && q  = p `And` q

-- | An infix alias for @And@.
type p ∧ q   = p `And` q

-- | An infix alias for @And@.
type p /\ q  = p `And` q

-- | An infix alias for @Implies@.
type p --> q = p `Implies` q

infixl 2 `Or`
infixl 2 ||
infixl 2 ∨
infixl 2 \/

infixl 3 `And`
infixl 3 &&
infixl 3 ∧
infixl 3 /\

infixr 1 `Implies`
infixr 1 -->

{--------------------------------------------------
  Mapping over conjunctions and disjunctions
--------------------------------------------------}

-- | Apply a derivation to the left side of a conjunction.
and_mapL :: (Proof p -> Proof p') -> Proof (p && q) -> Proof (p' && q)
and_mapL impl conj = let
  (lhs, rhs) = and_elim conj
  lhs' = impl lhs
  in and_intro lhs' rhs

-- | Apply a derivation to the right side of a conjunction.
and_mapR :: (Proof q -> Proof q') -> Proof (p && q) -> Proof (p && q')
and_mapR impl conj = let
  (lhs, rhs) = and_elim conj
  rhs' = impl rhs
  in and_intro lhs rhs'

-- | Apply derivations to the left and right sides of a conjunction.
and_map :: (Proof p -> Proof p') -> (Proof q -> Proof q') -> Proof (p && q) -> Proof (p' && q')
and_map implP implQ conj = let
  (lhs, rhs) = and_elim conj
  lhs' = implP lhs
  rhs' = implQ rhs
  in and_intro lhs' rhs'

-- | Apply a derivation to the left side of a disjunction.
or_mapL :: (Proof p -> Proof p') -> Proof (p || q) -> Proof (p' || q)
or_mapL impl = or_elim (or_introL . impl) or_introR

-- | Apply a derivation to the right side of a disjunction.
or_mapR :: (Proof q -> Proof q') -> Proof (p || q) -> Proof (p || q')
or_mapR impl = or_elim or_introL (or_introR . impl)

-- | Apply derivations to the left and right sides of a disjunction.
or_map :: (Proof p -> Proof p') -> (Proof q -> Proof q') -> Proof (p || q) -> Proof (p' || q')
or_map implP implQ = or_elim (or_introL . implP) (or_introR . implQ)

-- | Apply a derivation to the left side of an implication.
impl_mapL :: (Proof p' -> Proof p) -> Proof (p --> q) -> Proof (p' --> q)
impl_mapL derv impl = impl_intro (modus_ponens impl . derv)

-- | Apply a derivation to the right side of an implication.
impl_mapR :: (Proof q -> Proof q') -> Proof (p --> q) -> Proof (p --> q')
impl_mapR derv impl = impl_intro (derv . modus_ponens impl)

-- | Apply derivations to the left and right sides of an implication.
impl_map :: (Proof p' -> Proof p) -> (Proof q -> Proof q') -> Proof (p --> q) -> Proof (p' --> q')
impl_map dervL dervR impl = impl_intro (dervR . modus_ponens impl . dervL)

-- | Apply a derivation inside of a negation.
not_map :: (Proof p' -> Proof p) -> Proof (Not p) -> Proof (Not p')
not_map impl notP = not_intro (absurd . contradicts' notP . impl)

{--------------------------------------------------
  Tautologies
--------------------------------------------------}

-- | @TRUE@ is always true, and can be introduced into a proof at any time.
true :: Proof TRUE
true = axiom

-- | The Law of Noncontradiction: for any proposition P, "P and not-P" is false.
noncontra :: Proof (Not (p && Not p))
noncontra = axiom

{--------------------------------------------------
  Introduction rules
--------------------------------------------------}

-- | Prove "P and Q" from P and Q.
and_intro :: Proof p -> Proof q -> Proof (p && q)
and_intro _ _ = axiom

-- | Prove "P and Q" from Q and P.
and_intro' :: Proof q -> Proof p -> Proof (p && q)
and_intro' _ _ = axiom

-- | Prove "P or Q" from  P.
or_introL :: Proof p -> Proof (p || q)
or_introL _ = axiom

-- | Prove "P or Q" from Q.
or_introR :: Proof q -> Proof (p || q)
or_introR _ = axiom

-- | Prove "P implies Q" by demonstrating that,
--   from the assumption P, you can prove Q.
impl_intro :: (Proof p -> Proof q) -> Proof (p --> q)
impl_intro _ = axiom

-- | Prove "not P" by demonstrating that,
--   from the assumption P, you can derive a false conclusion.
not_intro :: (Proof p -> Proof FALSE) -> Proof (Not p)
not_intro _ = axiom

-- | `contrapositive` is an alias for `not_intro`, with
--   a somewhat more suggestive name. Not-introduction
--   corresponds to the proof technique "proof by contrapositive".
contrapositive :: (Proof p -> Proof FALSE) -> Proof (Not p)
contrapositive = not_intro

-- | Prove a contradiction from "P" and "not P".
contradicts :: Proof p -> Proof (Not p) -> Proof FALSE
contradicts _ _ = axiom

-- | `contradicts'` is `contradicts` with the arguments
--   flipped. It is useful when you want to partially
--   apply `contradicts` to a negation.
contradicts' :: Proof (Not p) -> Proof p -> Proof FALSE
contradicts' = flip contradicts

-- | Prove "For all x, P(x)" from a proof of P(*c*) with
--   *c* indeterminate.
univ_intro :: (forall c. Proof (p c)) -> Proof (ForAll x (p x))
univ_intro _ = axiom

-- | Prove "There exists an x such that P(x)" from a specific
--   instance of P(c).
ex_intro :: Proof (p c) -> Proof (Exists x (p x))
ex_intro _ = axiom

{--------------------------------------------------
  Elimination rules
--------------------------------------------------}

-- | From the assumption "P and Q", produce a proof of P.
and_elimL :: Proof (p && q) -> Proof p
and_elimL _ = axiom

-- | From the assumption "P and Q", produce a proof of Q.
and_elimR :: Proof (p && q) -> Proof q
and_elimR _ = axiom

-- | From the assumption "P and Q", produce both a proof
--   of P, and a proof of Q.
and_elim :: Proof (p && q) -> (Proof p, Proof q)
and_elim c = (and_elimL c, and_elimR c)

{-| If you have a proof of R from P, and a proof of
     R from Q, then convert "P or Q" into a proof of R.
-}
or_elim :: (Proof p -> Proof r) -> (Proof q -> Proof r) -> Proof (p || q) -> Proof r
or_elim _ _ _ = axiom

{-| Eliminate the first alternative in a conjunction.
-}
or_elimL :: (Proof p -> Proof r) -> Proof (p || q) -> (Proof q -> Proof r) -> Proof r
or_elimL case1 disj case2 = or_elim case1 case2 disj

{-| Eliminate the second alternative in a conjunction.
-}
or_elimR :: (Proof q -> Proof r) -> Proof (p || q) -> (Proof p -> Proof r) -> Proof r
or_elimR case2 disj case1 = or_elim case1 case2 disj

-- | Given "P imples Q" and P, produce a proof of Q.
--   (modus ponens)
impl_elim :: Proof p -> Proof (p --> q) -> Proof q
impl_elim _ _ = axiom

-- | @modus_ponens@ is just @impl_elim@ with the arguments
--   flipped. In this form, it is useful for partially
--   applying an implication.
modus_ponens :: Proof (p --> q) -> Proof p -> Proof q
modus_ponens = flip impl_elim

{-| Modus tollens lets you prove "Not P" from
    "P implies Q" and "Not Q".

    Modus tollens is not fundamental, and can be derived from
    other rules:

@
                                  -----         (assumption)
                        p --> q,    p
                       ---------------------    (modus ponens)
                 q,           Not q
              --------------------------        (contradicts')
                      FALSE
          ------------------------------------- (not-intro)
                             Not p
@

We can encode this proof tree more-or-less directly as a @Proof@
to implement @modus_tollens@:

@
modus_tollens :: Proof (p --> q) -> Proof (Not q) -> Proof (Not p)
modus_tollens impl q' = not_intro $ \p -> contradicts' q' (modus_ponens impl p)
@
-}

modus_tollens :: Proof (p --> q) -> Proof (Not q) -> Proof (Not p)
modus_tollens impl q' = not_intro $ \p -> contradicts' q' (modus_ponens impl p)

-- | From a falsity, prove anything.
absurd :: Proof FALSE -> Proof p
absurd _ = axiom

-- | Given "For all x, P(x)" and any c, prove the proposition
--   "P(c)".
univ_elim :: Proof (ForAll x (p x)) -> Proof (p c)
univ_elim _ = axiom

-- | Given a proof of Q from P(c) with c generic, and the
--   statement "There exists an x such that P(x)", produce
--   a proof of Q.
ex_elim :: (forall c. Proof (p c) -> Proof q) -> Proof (Exists x (p x)) -> Proof q
ex_elim _ _ = axiom


{--------------------------------------------------
  Classical logic
--------------------------------------------------}

-- | The inference rules so far have all been valid in
--   constructive logic. Proofs in classical logic are
--   also allowed, but will be constrained by the
--   `Classical` typeclass.
class Classical

-- | Discharge a @Classical@ constraint, by saying
--   "I am going to allow a classical argument here."
--
--   NOTE: The existence of this function means that a proof
--   should only be considered constructive if it
--   does not have a @Classical@ constraint, *and*
--   it does not invoke @classically@.
classically :: (Classical => Proof p) -> Proof p
classically _ = axiom

-- | The Law of the Excluded Middle: for any proposition
--   P, assert that either P is true, or Not P is true.
lem :: Classical => Proof (p || Not p)
lem = axiom

{-| Proof by contradiction: this proof technique allows
     you to prove P by showing that, from "Not P", you
     can prove a falsehood.

     Proof by contradiction is not a theorem of
     constructive logic, so it requires the @Classical@
     constraint. But note that the similar technique
     of proof by contrapositive (not-introduction) /is/
     valid in constructive logic! For comparison, the two types are:

@
contradiction  :: Classical => (Proof (Not p) -> Proof FALSE) -> Proof p
not_intro      ::              (Proof      p  -> Proof FALSE) -> Proof (Not p)
@

The derivation of proof by contradiction from the law of the excluded
middle goes like this: first, use the law of the excluded middle to
prove @p || Not p@. Then use or-elimination to prove @p@ for each
alternative. The first alternative is immediate; for the second
alternative, use the provided implication to get a proof of falsehood,
from which the desired conclusion is derived.

@
contradiction impl = or_elim id (absurd . impl) lem
@
-}
contradiction :: forall p. Classical => (Proof (Not p) -> Proof FALSE) -> Proof p
contradiction impl = or_elim id (absurd . impl) lem

{-| Double-negation elimination. This is another non-constructive
    proof technique, so it requires the @Classical@ constraint.

    The derivation of double-negation elimination follows from
    proof by contradiction, since "Not (Not p)" contradicts "Not p".
@
not_not_elim p'' = contradiction (contradicts' p'')
@
-}

not_not_elim :: Classical => Proof (Not (Not p)) -> Proof p
not_not_elim p'' = contradiction (contradicts' p'')

{--------------------------------------------------
  Algebraic properties
--------------------------------------------------}

instance Symmetric And
instance Symmetric Or

instance Associative And
instance Associative Or

instance DistributiveR And And
instance DistributiveR And Or
instance DistributiveR Or  And
instance DistributiveR Or  Or

instance DistributiveL And And
instance DistributiveL And Or
instance DistributiveL Or  And
instance DistributiveL Or  Or
