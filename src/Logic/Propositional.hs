{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

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
  , introAnd
  , introAnd'

  , introOrL
  , introOrR

  , introImpl
  , introNot

  , contrapositive
  , contradicts
  , contradicts'
  , introUniv
  , introEx

  -- *** Elimination rules

  -- | Elimination rules give the elementary building blocks for
  --   decomposing a complex formula into simpler ones.
  , elimAndL
  , elimAndR

  , elimOr
  , elimOrL
  , elimOrR

  , elimImpl
  , modusPonens
  , modusTollens
  , absurd
  , elimUniv
  , elimEx

  -- *** Classical logic and the Law of the Excluded Middle
  , Classical
  , classically
  , lem
  , contradiction
  , elimNot
  , elimNotNot

  -- *** Mapping over conjunctions and disjunctions.

  -- | These function names mimic the ones for
  -- (@Functor@/@Bifunctor@/@Profunctor@).
  , firstAnd
  , secondAnd
  , bimapAnd

  , firstOr
  , secondOr
  , bimapOr

  , lmapImpl
  , rmapImpl
  , dimapImpl

  , mapNot

  ) where

import Logic.Classes
import Logic.Proof

{--------------------------------------------------
  Logical constants
--------------------------------------------------}

-- | The constant "true".
data TRUE

-- | The constant "false".
data FALSE

-- | The conjunction of @p@ and @q@.
data And p q

-- | The disjunction of @p@ and @q@.
data Or p q

-- | The negation of @p@.
data Not p

-- | The implication "@p@ implies @q@".
data Implies p q

-- | Existential quantifiation.
data Exists x p

-- | Universal quantification.
data ForAll x p

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
firstAnd :: (Proof p -> Proof p') -> Proof (p && q) -> Proof (p' && q)
firstAnd = flip bimapAnd id

-- | Apply a derivation to the right side of a conjunction.
secondAnd :: (Proof q -> Proof q') -> Proof (p && q) -> Proof (p && q')
secondAnd = bimapAnd id

-- | Apply derivations to the left and right sides of a conjunction.
bimapAnd :: (Proof p -> Proof p') -> (Proof q -> Proof q') -> Proof (p && q) -> Proof (p' && q')
bimapAnd implP implQ conj = let
  (lhs, rhs) = elimAnd conj
  lhs' = implP lhs
  rhs' = implQ rhs
  in introAnd lhs' rhs'

-- | Apply a derivation to the left side of a disjunction.
firstOr :: (Proof p -> Proof p') -> Proof (p || q) -> Proof (p' || q)
firstOr = flip bimapOr id

-- | Apply a derivation to the right side of a disjunction.
secondOr :: (Proof q -> Proof q') -> Proof (p || q) -> Proof (p || q')
secondOr = bimapOr id

-- | Apply derivations to the left and right sides of a disjunction.
bimapOr :: (Proof p -> Proof p') -> (Proof q -> Proof q') -> Proof (p || q) -> Proof (p' || q')
bimapOr implP implQ = elimOr (introOrL . implP) (introOrR . implQ)

-- | Apply a derivation to the left side of an implication.
lmapImpl :: (Proof p' -> Proof p) -> Proof (p --> q) -> Proof (p' --> q)
lmapImpl = flip dimapImpl id

-- | Apply a derivation to the right side of an implication.
rmapImpl :: (Proof q -> Proof q') -> Proof (p --> q) -> Proof (p --> q')
rmapImpl = dimapImpl id

-- | Apply derivations to the left and right sides of an implication.
dimapImpl :: (Proof p' -> Proof p) -> (Proof q -> Proof q') -> Proof (p --> q) -> Proof (p' --> q')
dimapImpl dervL dervR impl = introImpl (dervR . modusPonens impl . dervL)

-- | Apply a derivation inside of a negation.
mapNot :: (Proof p' -> Proof p) -> Proof (Not p) -> Proof (Not p')
mapNot impl notP = introNot (absurd . contradicts' notP . impl)

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
introAnd :: Proof p -> Proof q -> Proof (p && q)
introAnd _ _ = axiom

-- | Prove "P and Q" from Q and P.
introAnd' :: Proof q -> Proof p -> Proof (p && q)
introAnd' _ _ = axiom

-- | Prove "P or Q" from  P.
introOrL :: Proof p -> Proof (p || q)
introOrL _ = axiom

-- | Prove "P or Q" from Q.
introOrR :: Proof q -> Proof (p || q)
introOrR _ = axiom

-- | Prove "P implies Q" by demonstrating that,
--   from the assumption P, you can prove Q.
introImpl :: (Proof p -> Proof q) -> Proof (p --> q)
introImpl _ = axiom

-- | Prove "not P" by demonstrating that,
--   from the assumption P, you can derive a false conclusion.
introNot :: (Proof p -> Proof FALSE) -> Proof (Not p)
introNot _ = axiom

-- | `contrapositive` is an alias for `introNot`, with
--   a somewhat more suggestive name. Not-introduction
--   corresponds to the proof technique "proof by contrapositive".
contrapositive :: (Proof p -> Proof FALSE) -> Proof (Not p)
contrapositive = introNot

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
introUniv :: (forall c. Proof (p c)) -> Proof (ForAll x (p x))
introUniv _ = axiom

-- | Prove "There exists an x such that P(x)" from a specific
--   instance of P(c).
introEx :: Proof (p c) -> Proof (Exists x (p x))
introEx _ = axiom

{--------------------------------------------------
  Elimination rules
--------------------------------------------------}

-- | From the assumption "P and Q", produce a proof of P.
elimAndL :: Proof (p && q) -> Proof p
elimAndL _ = axiom

-- | From the assumption "P and Q", produce a proof of Q.
elimAndR :: Proof (p && q) -> Proof q
elimAndR _ = axiom

-- | From the assumption "P and Q", produce both a proof
--   of P, and a proof of Q.
elimAnd :: Proof (p && q) -> (Proof p, Proof q)
elimAnd c = (elimAndL c, elimAndR c)

-- | If you have a proof of R from P, and a proof of R from Q, then
--   convert "P or Q" into a proof of R.
elimOr :: (Proof p -> Proof r) -> (Proof q -> Proof r) -> Proof (p || q) -> Proof r
elimOr _ _ _ = axiom

-- | Eliminate the first alternative in a conjunction.
elimOrL :: (Proof p -> Proof r) -> Proof (p || q) -> (Proof q -> Proof r) -> Proof r
elimOrL case1 disj case2 = elimOr case1 case2 disj

-- | Eliminate the second alternative in a conjunction.
elimOrR :: (Proof q -> Proof r) -> Proof (p || q) -> (Proof p -> Proof r) -> Proof r
elimOrR case2 disj case1 = elimOr case1 case2 disj

-- | Given "P imples Q" and P, produce a proof of Q.
--   (modus ponens)
elimImpl :: Proof p -> Proof (p --> q) -> Proof q
elimImpl _ _ = axiom

-- | @modusPonens@ is just `elimImpl` with the arguments
--   flipped. In this form, it is useful for partially
--   applying an implication.
modusPonens :: Proof (p --> q) -> Proof p -> Proof q
modusPonens = flip elimImpl

{-| Modus tollens lets you prove "Not P" from
    "P implies Q" and "Not Q".

    Modus tollens is not fundamental, and can be derived from
    other rules:

@
                                  -----         (assumption)
                        p --> q,    p
                       ---------------------    (modus ponens)
               Not q,            q
              --------------------------        (contradicts')
                      FALSE
          ------------------------------------- (not-intro)
                             Not p
@

We can encode this proof tree more-or-less directly as a @Proof@
to implement @modus_tollens@:

@
modusTollens :: Proof (p --> q) -> Proof (Not q) -> Proof (Not p)
modusTollens impl q' = introNot $ \p -> contradicts' q' (modusPonens impl p)
@
-}

modusTollens :: Proof (p --> q) -> Proof (Not q) -> Proof (Not p)
modusTollens impl q' = introNot $ \p -> contradicts' q' (modusPonens impl p)

-- | From a falsity, prove anything.
absurd :: Proof FALSE -> Proof p
absurd _ = axiom

-- | Given "For all x, P(x)" and any c, prove the proposition
--   "P(c)".
elimUniv :: Proof (ForAll x (p x)) -> Proof (p c)
elimUniv _ = axiom

-- | Given a proof of Q from P(c) with c generic, and the
--   statement "There exists an x such that P(x)", produce
--   a proof of Q.
elimEx :: (forall c. Proof (p c) -> Proof q) -> Proof (Exists x (p x)) -> Proof q
elimEx _ _ = axiom


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
introNot       ::              (Proof      p  -> Proof FALSE) -> Proof (Not p)
@

The derivation of proof by contradiction from the law of the excluded
middle goes like this: first, use the law of the excluded middle to
prove @p || Not p@. Then use or-elimination to prove @p@ for each
alternative. The first alternative is immediate; for the second
alternative, use the provided implication to get a proof of falsehood,
from which the desired conclusion is derived.

@
contradiction impl = elimOr id (absurd . impl) lem
@
-}
contradiction :: Classical => (Proof (Not p) -> Proof FALSE) -> Proof p
contradiction impl = elimOr id (absurd . impl) lem

-- | Alias for 'contradiction', to complete the patterns.
elimNot :: Classical => (Proof (Not p) -> Proof FALSE) -> Proof p
elimNot = contradiction

{-| Double-negation elimination. This is another non-constructive
    proof technique, so it requires the @Classical@ constraint.

    The derivation of double-negation elimination follows from
    proof by contradiction, since "Not (Not p)" contradicts "Not p".
@
elimNotNot p'' = contradiction (contradicts' p'')
@
-}

elimNotNot :: Classical => Proof (Not (Not p)) -> Proof p
elimNotNot p'' = contradiction (contradicts' p'')

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
