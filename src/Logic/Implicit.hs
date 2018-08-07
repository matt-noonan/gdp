{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Logic.Implicit
    ( Fact
    , known
    , note
    , on
    ) where

import           Logic.Proof
import           Theory.Named

import           Unsafe.Coerce

-- | A @Fact p@ is an implicit proof of @p@, propagated by Haskell's constraint solver.
--   @Fact@s can be used to implicitly introduce or propagate proofs. However, there is
--   a small run-time cost associated with using @Fact@s: typeclass dictionaries for
--   @Fact@s are still passed around. In many cases they will be optimized away, but this
--   is not guaranteed.
class Fact p

-- | Recall a known @Fact@ from the implicit context.
known :: Fact p => Proof p
known = axiom

newtype WithFact p t = WithFact (Fact p => t)

-- | Add a proof to the implicit context.
note :: forall p t. Proof p -> (Fact p => t) -> t
note _ k = unsafeCoerce (WithFact k :: WithFact p t) ()

{-| Apply an implication to a predicate in the implicit context. The @(a ~~ n)@
    parameter is not actually used; it's type is used to help select a specific
    fact from the context.

@
-- A safe 'head' function, using an implicitly-passed safety proof.
head :: Fact (IsCons xs) => ([a] ~~ xs) -> a
head xs = Prelude.head (the xs)

-- Reverse, and a lemma.
reverse :: ([a] ~~ xs) -> ([a] ~~ Reverse xs)
revConsLemma :: Proof (IsCons xs) -> Proof (IsCons (Reverse xs))

-- Implement a safe 'last' function.
last :: Fact (IsCons xs) => ([a] ~~ xs) -> a
last xs = note (revConsLemma `on` xs) $ head (reverse xs)
-}
on :: Fact (p n) => (Proof (p n) -> Proof q) -> (a ~~ n) -> Proof q
on impl _ = impl known
