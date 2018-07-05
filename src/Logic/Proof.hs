{-# LANGUAGE KindSignatures #-}

{-|
  Module      :  Logic.Proof
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Logic.Proof
  ( -- * The `Proof` type
    Proof
  , axiom, sorry
  ) where

{--------------------------------------------------
  The `Proof` type
--------------------------------------------------}

{-| The @Proof@ type is used as a domain-specific
    language for constructing proofs. A value of type
    @Proof p@ represents a proof of the proposition @p@.

    A @Proof@ as an argument to a function represents an
    assumption. For example, this function constructions a proof of "P
    or Q" from the assumption "P and Q":

> and2or :: Proof (p && q) -> Proof (p || q)
>
> and2or pq = introOrL $ elimAndL pq

    If the body of the proof does not match the proposition
    you claim to be proving, the compiler will raise a type
    error. Here, we accidentally try to use @or_introR@
    instead of @or_introL@:

> and2or :: Proof (p && q) -> Proof (p || q)
>
> and2or pq = introOrR $ elimAndL pq

resulting in the error

@
    • Couldn't match type ‘p’ with ‘q’
      ‘p’ is a rigid type variable bound by
        the type signature for:
          and2or :: forall p q. Proof (p && q) -> Proof (p || q)

      ‘q’ is a rigid type variable bound by
        the type signature for:
          and2or :: forall p q. Proof (p && q) -> Proof (p || q)

      Expected type: Proof (p || q)
        Actual type: Proof (p || p)
@
-}
data Proof (pf :: *) = QED

-- | @sorry@ can be used to provide a "proof" of
--   any proposition, by simply assering it as
--   true. This is useful for stubbing out portions
--   of a proof as you work on it, but subverts
--   the entire proof system.
--
-- _Completed proofs should never use @sorry@!_
sorry :: Proof p
sorry = QED
{-# WARNING sorry "Completed proofs should never use sorry!" #-}

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
