{-# LANGUAGE KindSignatures #-}

{-|
  Module      :  Logic.Proof
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Logic.Proof
  ( -- * The `Proof` monad
    Proof
  , (|.), (|$), (|/), (|\), ($$)
  , given
  , axiom, sorry
  ) where

import Data.Coerce
import Control.Monad ((>=>))

{--------------------------------------------------
  The `Proof` monad
--------------------------------------------------}

{-| The @Proof@ monad is used as a domain-specific
    language for constructing proofs. A value of type
    @Proof p@ represents a proof of the proposition @p@.

    For example, this function constructions a proof of
    "P or Q" from the assumption "P and Q":

> and2or :: (p && q) -> Proof (p || q)
>
> and2or pq = do
>    p <- and_elimL pq    -- or: "p <- fst <$> and_elim pq"
>    or_introL p

    If the body of the proof does not match the proposition
    you claim to be proving, the compiler will raise a type
    error. Here, we accidentally try to use @or_introR@
    instead of @or_introL@:

> and2or :: (p && q) -> Proof (p || q)
>
> and2or pq = do
>    p <- and_elimL pq
>    or_introR p

resulting in the error

@
    • Couldn't match type ‘p’ with ‘q’
      ‘p’ is a rigid type variable bound by
        the type signature for:
          and2or :: forall p q. (p && q) -> Proof (p || q)

      ‘q’ is a rigid type variable bound by
        the type signature for:
          and2or :: forall p q. (p && q) -> Proof (p || q)

      Expected type: Proof (p || q)
        Actual type: Proof (p || p)
@
-}
data Proof (pf :: *) = QED

instance Functor Proof where
  fmap _ = const QED -- modus ponens (external?)

instance Applicative Proof where
  pure = const QED -- axiom
  pf1 <*> pf2 = QED -- modus ponens (internal?)

instance Monad Proof where
  pf >>= f = QED

{-| This operator is just a specialization of @(>>=)@, but
    can be used to create nicely delineated chains of
    derivations within a larger proof. The first statement
    in the chain should produce a formula; @(|$)@ then
    pipes this formula into the following derivation rule.

> and2or :: (p && q) -> Proof (p || q)
>
> and2or pq =  and_elimL pq
>           |$ or_introL
-}

(|$) :: Proof p -> (p -> Proof q) -> Proof q
(|$) = (>>=)

infixr 7 |$

--(|-) :: ((p -> Proof r) -> Proof r) -> (p -> Proof r) -> Proof r

{-| This operator is used to create nicely delineated chains of
    derivations within a larger proof. If X and Y are two
    deduction rules, each with a single premise and a single
    conclusion, and the premise of Y matches the conclusion of X,
    then @X |. Y@ represents the composition of the two
    deduction rules.

> and2or :: (p && q) -> Proof (p || q)
>
> and2or =  and_elimL
>        |. or_introL
-}

(|.) :: (p -> Proof q) -> (q -> Proof r) -> p -> Proof r
(|.) = (>=>)

infixr 9 |.

{-| The @(|/)@ operator is used to feed the remainder of the proof in
    as a premise of the first argument.

    A common use-case is with the @Or@-elimination rules @or_elimL@ and
    @or_elimR@, when one case is trivial. For example, suppose we wanted
    to prove that @R && (P or (Q and (Q implies P)))@ implies @P@:

@
my_proof :: r && (p || (q && (q --> p))) -> Proof p

my_proof =
  do  and_elimR          -- Forget the irrelevant r.
   |. or_elimL given     -- The first case of the || is immediate;
   |/ and_elim           -- The rest of the proof handles the second case,
   |. uncurry impl_elim  --   by unpacking the && and feeding the q into
                         --   the implication (q --> p).
@

    The rising @/@ is meant to suggest the bottom half of the proof getting
    plugged in to the Or-elimination line.
-}
(|/) :: (p -> (q -> Proof r) -> Proof r) -> (q -> Proof r) -> p -> Proof r
(|/) = flip
infixr 9 |/

{-| The @(|\\)@ operator is used to take the subproof so far and feed it
    into a rule that is expecting a subproof as a premise.

    A common use-case is with the @Not@-introduction rule @not_intro@,
    which has a type that fits the second argument of @(|\\)@. By way
    of example, here is a proof that "P implies Q" along with "Not Q"
    implies "Not P".

@
my_proof :: (p --> q) -> (Not p --> r) -> Not q -> Proof r

my_proof impl1 impl2 q' =
  do  modus_ponens impl1   -- This line, composed with the next,
   |. contradicts' q'      --   form a proof of FALSE from p.
   |\\ not_intro            -- Closing the subproof above, conclude not-p.
   |. modus_ponens impl2   -- Now apply the second implication to conclude r.
@

    The falling @\\@ is meant to suggest the upper half of the proof
    being closed off by the Not-introduction line.
-}
(|\) :: (p -> Proof q) -> ((p -> Proof q) -> Proof r) -> Proof r
(|\) = flip ($)
infixl 8 |\

-- | Take a proof of @p@ and feed it in as the first premise of
--   an argument that expects a @p@ and a @q@.
($$) :: (p -> q -> Proof r) -> Proof p -> (q -> Proof r)
(f $$ pp) q = do { p <- pp; f p q }

-- | @given@ creates a proof of P, given P as
--   an assumption.
--
--   @given@ is just a specialization of @pure@ / @return@.
given :: p -> Proof p
given _ = QED

-- | @sorry@ can be used to provide a "proof" of
--   any proposition, by simply assering it as
--   true. This is useful for stubbing out portions
--   of a proof as you work on it, but subverts
--   the entire proof system.
--
-- _Completed proofs should never use @sorry@!_
sorry :: Proof p
sorry = QED

{-| @axiom@, like @sorry@, provides a "proof" of any
    proposition. Unlike @sorry@, which is used to indicate
    that a proof is still in progress, @axiom@ is meant to
    be used by library authors to assert axioms about how
    their library works. For example:

@
data Reverse xs = Reverse Defn
data Length  xs = Length  Defn

rev_length_lemma :: Proof (Length (Reverse xs) == Length xs)
rev_length_lemma = axiom
@
-}
axiom :: Proof p
axiom = QED

