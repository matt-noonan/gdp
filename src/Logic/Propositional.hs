{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}

module Logic.Propositional
  (
  -- * The `Proof` monad
    Proof
  , (|.), (|$), (|/), (|\), ($$)
  , given
  , sorry

  -- * Refinement types
  , (:::)
  , the
  , ($.)
  , via
  , by
  , because

  , inject
  , inject'

  , impossible
  , contradictory
  , contradictory'
  
  , toSpec
  , toSpecPxy
  
  -- * First-order Logic

  -- ** Logical symbols
  , TRUE, FALSE
  
  , And, type (∧), type (/\), type (&&)
  , Or,  type (∨), type (\/), type (||)
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

  -- *** Mapping over conjunctions and disjunctions
  , and_mapL
  , and_mapR
  , and_map

  , or_mapL
  , or_mapR
  , or_map

  -- *** Classical logic and the Law of the Excluded Middle
  , Classical
  , lem

  -- * Algebraic properties
  , Reflexive(..)
  , Irreflexive(..)
  , Symmetric(..)
  , Antisymmetric(..)
  , Transitive(..)
  , transitive'

  , Idempotent(..)
  , Commutative(..)
  , Associative(..)
  , Distributive(..)

  , Injective(..)

  -- * Theory of Identity and Equality
  , Is, type (~~)
  , nameless
  , using
  , using2
  , named
  , named2
  , bare
  , (&&.)
  , is_also
  , is_also'
  , Equals
  , type (==)
  , type (/=)
  , Arg(..)
  , arg
  , Argument(..)
  , substitute
  , substituteL
  , substituteR
  , apply

  -- * Pattern matching
  , Cases(..)
  , defCase
  , (<+>)
  , toDef
  , Match, MCons, MName, MGuard, AlsoGuard, Matchy(..)
  
  -- * User-defined theories
  , Defn, Defining
  , UserType
  , defining, defining2, defining2'
  , assert_decomp2
  , guard0, guard1, guard2

  -- * unclassified stuff

  , Exist(..)
  , ForAll'
  , univ_qed'
  , univ_elim'

  , assert
  , assert2
  , qed
  , qed2
  , assert_is
  , assert_is1
  , assert_is2
  , assertNot
  , assertNot2
  , decompose1
  , decompose2
  , qedNot
  , qedNot2
  , qedEq
  , qedEq'0
  , qedEq'1
  , qedEq'2
  , qedNotEq
  , assertEq
  , assertNotEq

{-
, Of
  , type ($)
  , ap
  , ($.)
-}
)
  where

import Logic.Arguments
import Tactics

import Data.Coerce
import Unsafe.Coerce
import Data.Proxy

import Control.Monad ((>=>))
import Control.Applicative ((<|>))
import Data.Maybe (mapMaybe)

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

my_proof' :: r && (p || (q && (q --> p))) -> Proof p

my_proof' = do  and_elimR
             |. or_elimL given
             |/ and_elim
             |. uncurry impl_elim

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
  
my_proof :: (p --> q) -> (Not p --> r) -> Not q -> Proof r

my_proof impl1 impl2 q' =
  do modus_ponens impl1    -- This line, composed with the next,
  |. contradicts' q'       --   form a proof of FALSE from p.
  |\ not_intro             -- Closing the subproof above, conclude not-p.
  |. modus_ponens impl2

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

inject :: Proof p -> a -> (a ::: p)
inject _ = coerce

inject' :: Proof p -> (a ::: q) -> (a ::: p && q)
inject' _ = coerce

class Prop a p | a -> p where
  getProp :: a -> Proof p

instance Prop (a ~~ n ::: p) p where
  getProp _ = QED

instance Prop (a ~~ n) TRUE where
  getProp _ = QED
  
instance (Prop b q) => Prop ((a ~~ n ::: p) -> b) (p --> q) where
  getProp = error "Todo" -- getProp @b @q


{--------------------------------------------------
  Refinement types
--------------------------------------------------}

{-| Given a type @a@ and a proposition @p@, the
    type @(a ::: p)@ represents a /refinement type/
    for @a@. Values of type @(a ::: p)@ are values
    of type @a@ such that proposition @p@ holds.

    Values of the refinement type @(a ::: p)@ have
    the same run-time representation as values of
    the normal type @a@; the proposition @p@ does
    not carry a run-time space or time cost.

    By design, there are no functions to extract
    the @p@ from a @(a ::: p)@.
-}
newtype a ::: p = Value a
infixr 1 :::

-- | @the@ lets you forget about a refinement, resulting
--   in a normal, unrefined value.
the :: (a ::: p) -> a
the = coerce

($.) :: (a -> b) -> (a ::: p) -> b
f $. x = f (the x)

infixr 0 $.
  
-- | Given a value with refinement type @(a ::: p)@ and
--   a proof that @p@ implies @q@, get a value with
--   refinement type @(a ::: q)@.
--
--   In fact, this will be the exact same value you
--   started with: @the value@ has the same run-time
--   representation as @the (value \`via\` impl)@.
--   Usually, these will even represent the same
--   location in memory.
via :: (a ::: p) -> Proof (p --> q) -> (a ::: q)
x `via` _ = coerce x

-- | @by@ is a useful variation of @via@, for when you have
--   a proof of @q@ given @p@ but haven't packed it into
--   an implication.
--
-- > just_p :: (a ::: p ∧ q) -> (a ::: p)
-- > just_p x = x `by` and_elimL

by ::  (a ::: p) -> (p -> Proof q) -> (a ::: q)
x `by` proof = x `via` impl_intro proof

-- | @because@ is yet another variation of @via@ and @by@.
--   It is useful in situations where you would like
--   to partially apply @by@ by filling in the proof of @q@
--   given @p@.
--
-- > just_p :: (a ::: p ∧ q) -> (a ::: p)
-- > just_p = because and_elimL

because :: (p -> Proof q) -> (a ::: p) -> (a ::: q)
because _ = coerce

impossible :: (a ::: FALSE) -> b
impossible _ = error "impossible"

contradictory :: (a ~~ name ::: p) -> (a ~~ name ::: Not p) -> b
contradictory _ _ = error "contradictory"

contradictory' :: (a ~~ name ::: Not p) -> (a ~~ name ::: p) -> b
contradictory' _ _ = error "contradictory'"

class HasSpec a where
  type family Spec a :: *

{-| `toSpec` lets you get a formula
    representing the formal specification of a function.
 
    For example, consider a safe variation on the `tail`
    function that can only be used when the input list has
    nonzero length:
 
> tail :: ([a] ~~ xs      ::: Length xs == Succ n)
>      -> ([a] ~~ Tail xs ::: Length (Tail xs) == n)

    Then @toSpec tail@ will produce a proof of type

> toSpec tail :: Proof (Length xs == Succ n --> Length (Tail xs) == n)

> cons :: (a ~~ x)
>      -> ([a] ~~ xs)
>      -> ([a] ~~ Cons x xs ::: Head   (Cons x xs) == x
>                            && Tail   (Cons x xs) == xs
>                            && Length (Cons x xs) == Succ (Length xs))

> toSpec cons :: Proof (  Head   (Cons x xs) == x)
>                      && Tail   (Cons x xs) == xs)
>                      && Length (Cons x xs) == Succ (Length xs) )

> reverse :: ([a] ~~ xs)
>         -> ([a] ~~ Reverse xs ::: Length (Reverse xs) == Length xs)

> toSpec reverse :: Proof ( Length (Reverse xs) == Length xs )


   Let's put all of these parts together to show that @tail (reverse (cons x xs))@
   is safe!

>  tailRevCons :: a -> [a] -> [a]
> 
-}

toSpec :: HasSpec a => a -> Proof (Spec a)
toSpec _ = QED

toSpecPxy :: HasSpec a => Proxy a -> Proof (Spec a)
toSpecPxy _ = QED

instance HasSpec b => HasSpec ((a ::: p) -> b) where
  type Spec ((a ::: p) -> b) = p --> Spec b

instance HasSpec b => HasSpec ((a ~~ n) -> b) where
  type Spec ((a ~~ n) -> b) = Spec b
  
instance HasSpec (a ::: (p :: *)) where
  type Spec (a ::: p) = p

{--------------------------------------------------
  Logical symbols
--------------------------------------------------}

-- | The constant "TRUE".
newtype TRUE = TRUE Defn

-- | The constant "FALSE", representing an absurd or impossible conclusion.
newtype FALSE = FALSE Defn

-- | @p `And` q@ represents the conjunction of @p@ and @q@. @p `And` q@ is true
--   when both @p@ and @q@ are true.
--
--   You may also use @∧@, @/\@, and @&&@ as infix operators for @And@.
newtype And p q = And Defn
infixl 3 `And`

type p ∧ q   = And p q
infixl 3 ∧

type p /\ q  = And p q
infixl 3 /\

type p && q = And p q
infixl 3 &&

instance Argument (And x y) 0 where
  type GetArg (And x y) 0    = x
  type SetArg (And x y) 0 x' = And x' y
  
instance Argument (And x y) 1 where
  type GetArg (And x y) 1    = x
  type SetArg (And x y) 1 x' = And x' y
  

-- | @p `Or` q@ represents the disjunction of @p@ and @q@. @p `Or` q@ is true
--   when either @p@ is true or @q@ is true.
--
--   You may also use @∨@, @\/@, and @||@ as infix operators for @Or@.
newtype Or  p q = Or  Defn
infixl 2 `Or`

type p ∨ q   = Or  p q
infixl 2 ∨

type p \/ q  = Or p q
infixl 2 \/

type p || q  = Or p q
infixl 2 ||

instance Argument (Or x y) 0 where
  type GetArg (Or x y) 0    = x
  type SetArg (Or x y) 0 x' = Or x' y
  
instance Argument (Or x y) 1 where
  type GetArg (Or x y) 1    = x
  type SetArg (Or x y) 1 x' = Or x' y  

-- | @Not p@ represents the logical negation of @p@. @Not p@ is true only when
--   @p@ is false.
newtype Not p   = Not Defn

instance Argument (Not x) 0 where
  type GetArg (Not x) 0    = x
  type SetArg (Not x) 0 x' = Not x'

-- | @p `Implies` q@ represents implication. @p `Implies` q@ is true if, when
--   @p@ is true, then @q@ is true as well.
--
--   You may also use @-->@ as an infix operator for @Implies@.
--
--   @p `Implies` q@ is entirely equivalent to @q || Not p@, but is provided
--   for convenience and clarity.
newtype Implies p q = Implies Defn
type p --> q = Implies p q

infixr 1 -->

instance Argument (Implies x y) 0 where
  type GetArg (Implies x y) 0    = x
  type SetArg (Implies x y) 0 x' = Implies x' y
  
instance Argument (Implies x y) 1 where
  type GetArg (Implies x y) 1    = x
  type SetArg (Implies x y) 1 x' = Implies x' y  

newtype ForAll x p = ForAll Defn

instance Argument p n => Argument (ForAll x p) n where
  type GetArg (ForAll x p) n    = GetArg p n
  type SetArg (ForAll x p) n p' = ForAll x (SetArg p n p')

newtype Exists x p = Exists Defn

instance Argument p n => Argument (Exists x p) n where
  type GetArg (Exists x p) n    = GetArg p n
  type SetArg (Exists x p) n p' = Exists x (SetArg p n p')

{--------------------------------------------------
  Tautologies
--------------------------------------------------}

-- | @TRUE@ is always true, and can be introduced into a proof at any time.
true :: Proof TRUE
true = QED

-- | The Law of Noncontradiction: for any proposition P, "P and not-P" is false.
noncontra :: Proof (Not (p ∧ Not p))
noncontra = QED

{--------------------------------------------------
  Introduction rules
--------------------------------------------------}

-- | Prove "P and Q" from P and Q.
and_intro :: p -> q -> Proof (p ∧ q)
and_intro _ _ = QED

-- | Prove "P and Q" from Q and P.
and_intro' :: q -> p -> Proof (p ∧ q)
and_intro' _ _ = QED

-- | Prove "P or Q" from  P.
or_introL :: p -> Proof (p ∨ q)
or_introL _ = QED

-- | Prove "P or Q" from Q.
or_introR :: q -> Proof (p ∨ q)
or_introR _ = QED

-- | Prove "P implies Q" by demonstrating that,
--   from the assumption P, you can prove Q.
impl_intro :: (p -> Proof q) -> Proof (p --> q)
impl_intro _ = QED

-- | Prove "not P" by demonstrating that,
--   from the assumption P, you can derive a false conclusion.
not_intro :: (p -> Proof FALSE) -> Proof (Not p)
not_intro _ = QED

-- | `contrapositive` is an alias for `not_intro`, with
--   a somewhat more suggestive name. Not-introduction
--   corresponds to the proof technique "proof by contrapositive".
contrapositive :: (p -> Proof FALSE) -> Proof (Not p)
contrapositive = not_intro

-- | Prove a contradiction from "P" and "not P".
contradicts :: p -> Not p -> Proof FALSE
contradicts _ _ = QED

-- | `contradicts'` is `contradicts` with the arguments
--   flipped. It is useful when you want to partially
--   apply `contradicts` to a negation.
contradicts' :: Not p -> p -> Proof FALSE
contradicts' = flip contradicts

-- | Prove "For all x, P(x)" from a proof of P(*c*) with
--   *c* indeterminate.
univ_intro :: (forall c. Proof (p c)) -> Proof (ForAll x (p x))
univ_intro _ = QED

-- | Prove "There exists an x such that P(x)" from a specific
--   instance of P(c).
ex_intro :: p c -> Proof (Exists x (p x))
ex_intro _ = QED

{--------------------------------------------------
  Elimination rules
--------------------------------------------------}

-- | From the assumption "P and Q", produce a proof of P.
and_elimL :: p ∧ q -> Proof p
and_elimL _ = QED

-- | From the assumption "P and Q", produce a proof of Q.
and_elimR :: p ∧ q -> Proof q
and_elimR _ = QED

-- | From the assumption "P and Q", produce both a proof
--   of P, and a proof of Q.
and_elim :: p ∧ q -> Proof (p, q)
and_elim c = (,) <$> and_elimL c <*> and_elimR c
  
{-| If you have a proof of R from P, and a proof of
     R from Q, then convert "P or Q" into a proof of R.
-}
or_elim :: (p -> Proof r) -> (q -> Proof r) -> (p ∨ q) -> Proof r
or_elim _ _ _ = QED

{-| Eliminate the first alternative in a conjunction.
-}
or_elimL :: (p -> Proof r) -> (p ∨ q) -> (q -> Proof r) -> Proof r
or_elimL case1 disj case2 = or_elim case1 case2 disj

{-| Eliminate the second alternative in a conjunction.
-}
or_elimR :: (q -> Proof r) -> (p ∨ q) -> (p -> Proof r) -> Proof r
or_elimR case2 disj case1 = or_elim case1 case2 disj

-- | Given "P imples Q" and P, produce a proof of Q.
--   (modus ponens)
impl_elim :: p -> (p --> q) -> Proof q
impl_elim _ _ = QED

-- | @modus_ponens@ is just @impl_elim@ with the arguments
--   flipped. In this form, it is useful for partially
--   applying an implication.
modus_ponens :: (p --> q) -> p -> Proof q
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
modus_tollens :: (p --> q) -> Not q -> Proof (Not p)

modus_tollens impl q' =
  do  modus_ponens impl
   |. contradicts' q'
   |\\ not_intro
@
-}

modus_tollens :: (p --> q) -> Not q -> Proof (Not p)
modus_tollens impl q' =
  do  modus_ponens impl
   |. contradicts' q'
   |\ not_intro

-- | From a falsity, prove anything.
absurd :: FALSE -> Proof p
absurd _ = QED

-- | Given "For all x, P(x)" and any c, prove the proposition
--   "P(c)".
univ_elim :: ForAll x (p x) -> Proof (p c)
univ_elim _ = QED

-- | Given a proof of Q from P(c) with c generic, and the
--   statement "There exists an x such that P(x)", produce
--   a proof of Q.
ex_elim :: (forall c. p c -> Proof q) -> Exists x (p x) -> Proof q
ex_elim _ _ = QED

{--------------------------------------------------
  Mapping over conjunctions and disjunctions
--------------------------------------------------}

and_mapL :: (p -> Proof p') -> (p && q) -> Proof (p' && q)
and_mapL impl conj = do
  (lhs, rhs) <- and_elim conj
  lhs' <- impl lhs
  and_intro lhs' rhs

and_mapR :: (q -> Proof q') -> (p && q) -> Proof (p && q')
and_mapR impl conj = do
  (lhs, rhs) <- and_elim conj
  rhs' <- impl rhs
  and_intro lhs rhs'

and_map :: (p -> Proof p') -> (q -> Proof q') -> (p && q) -> Proof (p' && q')
and_map implP implQ conj = do
  (lhs, rhs) <- and_elim conj
  lhs' <- implP lhs
  rhs' <- implQ rhs
  and_intro lhs' rhs'


or_mapL :: (p -> Proof p') -> (p || q) -> Proof (p' || q)
or_mapL impl = or_elim (impl |. or_introL) or_introR

or_mapR :: (q -> Proof q') -> (p || q) -> Proof (p || q')
or_mapR impl = or_elim or_introL (impl |. or_introR)

or_map :: (p -> Proof p') -> (q -> Proof q') -> (p || q) -> Proof (p' || q')
or_map implP implQ = or_elim (implP |. or_introL) (implQ |. or_introR)

{--------------------------------------------------
  Classical logic
--------------------------------------------------}

-- | The inference rules so far have all been valid in
--   constructive logic. Proofs in classical logic are
--   also allowed, but will be constrained by the
--   `Classical` typeclass.
class Classical

-- | The Law of the Excluded Middle: for any proposition
--   P, assert that either P is true, or Not P is true.
lem :: Classical => Proof (p ∨ Not p)
lem = QED

{-| Proof by contradiction: this proof technique allows
     you to prove P by showing that, from "Not P", you
     can prove a falsehood.
  
     Proof by contradiction is not a theorem of
     constructive logic, so it requires the @Classical@
     constraint. But note that the similar technique
     of proof by contrapositive (not-introduction) /is/
     valid in constructive logic! For comparison, the two types are:

@
contradiction  :: Classical => (Not p -> Proof FALSE) -> p
not_intro      ::              (p     -> Proof FALSE) -> Not p
@

The derivation of proof by contradiction from the law of the excluded
middle goes like this: first, use the law of the excluded middle to
prove @p || Not p@. Then use or-elimination to prove @p@ for each
alternative. The first alternative is immediate; for the second
alternative, use the provided implication to get a proof of falsehood,
from which the desired conclusion is derived.

@
contradiction impl =
  do  lem             -- introduce p || Not p
   |$ or_elimL given  -- dispatch the first, straightforward case
   |/ impl            -- Now we're on the second case. Apply the implication..
   |. absurd          -- .. and, from falsity, conclude p.
@
-}
contradiction :: forall p. Classical => (Not p -> Proof FALSE) -> Proof p
contradiction impl =
  do  lem
   |$ or_elimL given
   |/ impl
   |. absurd
  
{-| Double-negation elimination. This is another non-constructive
    proof technique, so it requires the @Classical@ constraints.

    The derivation of double-negation elimination follows from
    proof by contradiction, since "Not (Not p)" contradicts "Not p".
@
not_not_elim p'' = contradiction (contradicts' p'')
@
-}

not_not_elim :: Classical => Not (Not p) -> Proof p
not_not_elim p'' = contradiction (contradicts' p'')

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
newtype SameColor p q = SameColor Defn
instance Reflexive SameColor
@
-}   
class Reflexive r where
  refl :: Proof (r x x)
  default refl :: (Defining (r x x)) => Proof (r x x)
  refl = QED

class Irreflexive r where
  irrefl :: Proof (Not (r x x))
  default irrefl :: (Defining (r x x)) => Proof (Not (r x x))
  irrefl = QED

{-| A binary relation R is /symmetric/ if, for all x and y,
    R(x, y) is true if and only if R(y, x) is true. The
    @Symmetric@ typeclass provides
    a single method, @symmetric :: r x y -> Proof (r y x)@,
    proving the implication "R(x, y) implies R(y, x)".

    Within the module where @R@ is defined, you can
    declare @R@ to be symmetric with an empty instance:

@
-- Define a symmetric binary relation
newtype NextTo p q = NextTo Defn
instance Symmetric NextTo
@
-}   
class Symmetric c where
  symmetric :: c p q -> Proof (c q p)
  default symmetric :: (Defining (c p q)) => c p q -> Proof (c q p)
  symmetric _ = QED

class Antisymmetric c where
  antisymmetric :: c p q -> Proof (Not (c q p))
  default antisymmetric :: Defining (c p q) => c p q -> Proof (Not (c q p))
  antisymmetric _ = QED
  
  antisymmetric' :: Not (c p q) -> Proof (c q p)
  default antisymmetric' :: Defining (c p q) => Not (c p q) -> Proof (c q p)
  antisymmetric' _ = QED

  
{-| A binary relation R is /transitive/ if, for all x, y, z,
    if R(x, y) is true and R(y, z) is true, then  R(x, z) is true.
    The @Transitive r@ typeclass provides
    a single method, @transitive :: r x y -> r y z -> Proof (r x z)@,
    proving R(x, z) from R(x, y) and R(y, z).

    Within the module where @R@ is defined, you can
    declare @R@ to be transitive with an empty instance:

@
-- Define a transitive binary relation
newtype CanReach p q = CanReach Defn
instance Transitive CanReach
@
-}   
class Transitive c where
  transitive :: c p q -> c q r -> Proof (c p r)
  default transitive :: Defining (c p q) => c p q -> c q r -> Proof (c p r)
  transitive _ _ = QED

transitive' :: Transitive c => c q r -> c p q -> Proof (c p r)
transitive' = flip transitive

class Idempotent c where
  idempotent :: Proof (c p p == p)
  default idempotent :: Defining (c p p) => Proof (c p p == p)
  idempotent = QED
  
class Commutative c where
  
  commutative :: Proof (c p q == c q p)
  default commutative :: Defining (c p q) => Proof (c p q == c q p)
  commutative = QED
  
  commute :: c p q -> c q p
  default commute :: (Defining (c p q), Defining (c q p)) => c p q -> c q p
  commute = by_defn

class Associative c where

  associative :: Proof (c p (c q r) == c (c p q) r)
  default associative :: Defining (c p q) => Proof (c p (c q r) == c (c p q) r)
  associative = QED
  
  assocL :: c p (c q r) -> c (c p q) r
  default assocL :: (Defining (c p (c q r)), Defining (c (c p q) r)) => c p (c q r) -> c (c p q) r
  assocL = by_defn
  assocR :: c (c p q) r -> c p (c q r)
  default assocR :: (Defining (c (c p q) r), Defining (c p (c q r)))  => c (c p q) r -> c p (c q r)
  assocR = by_defn

class Distributive c c' where

  distributive :: Proof (c p (c' q r) == c' (c p q) (c p r))
  default distributive :: (Defining (c p q), Defining (c' p q)) => Proof (c p (c' q r) == c' (c p q) (c p r))
  distributive = QED

class Injective c where
  elim_inj :: (c (f x) == c (f y)) -> Proof (c x == c y)
  default elim_inj :: (Defining (c (f x)), Defining (c (f y)), Defining (c x), Defining (c y))
   => (c (f x) == c (f y)) -> Proof (c x == c y)
  elim_inj _ = QED
  
{--------------------------------------------------
  Algebraic properties
--------------------------------------------------}

instance Symmetric And
instance Symmetric Or

instance Associative And
instance Associative Or

instance Distributive And And
instance Distributive And Or
instance Distributive Or  And
instance Distributive Or  Or

instance Simplifiable p p' => Simplifiable (a ~~ n ::: p) (a ~~ n ::: p')
--where simplfiy x = coerce x

instance Simplifiable (TRUE  `And` p    ) p
instance Simplifiable (p     `And` TRUE ) p
instance Simplifiable (FALSE `And` p    ) FALSE
instance Simplifiable (p     `And` FALSE) FALSE

instance Simplifiable (TRUE  `Or` p    ) TRUE
instance Simplifiable (p     `Or` TRUE ) TRUE
instance Simplifiable (FALSE `Or` p    ) p
instance Simplifiable (p     `Or` FALSE) p

instance Simplifiable (Not (Not p)) p

instance Simplifiable (p `And` p) p
instance Simplifiable (p `Or`  p) p

instance Simplifiable (p `Implies` q) (q `Or` Not p)

{--------------------------------------------------
  Pattern matching
--------------------------------------------------}

-- | The @Cases@ typeclass is used to destructure an
--   inductive type, by matching a case against a pattern.
class Cases pat cs r where
  cases :: pat -> cs -> Proof r

defCase :: Matchy (Proxy g, t) (AlsoGuard' g m) t =>
  Proxy g -> (x -> Bool) -> (x -> t) -> (x -> Maybe (Match (AlsoGuard (g, m)) t))
defCase pxy guard body = \x -> if guard x then Just (mkCase (pxy, body x)) else Nothing
  
mkCase :: Matchy (Proxy g, f) (AlsoGuard' g m) t => (Proxy g, f) -> Match (AlsoGuard (g, m)) t
mkCase = unrollAlsoGuard . mkCase'

type CaseList x t = [x -> Maybe (SomeCase t)]

newtype CtorTest g x = CtorTest (x -> Bool)

runMatch :: CaseList x t -> x -> t
runMatch fs x = case mapMaybe ($x) fs of
  (SomeCase y : _) -> coerce y
  [] -> error "ran out of cases!"

defCase' :: Matchy (Proxy g, t) (AlsoGuard' g m) t =>
  Proxy g -> (x -> Bool) -> (x -> t) -> (x -> Maybe t, Proxy (AlsoGuard (g,m)))
defCase' pxy guard body = (\x -> if guard x then Just (body x) else Nothing, Proxy)

(<+>) :: (x -> Maybe (Match (AlsoGuard (g, m)) t))
     -> (x -> Maybe (Match (AlsoGuard (g',m')) t))
     -> (x -> Maybe (Match ((MCons (AlsoGuard (g, m)) (AlsoGuard (g',m')))) t))
p1 <+> p2 = (\x -> coerce (p1 x) <|> coerce (p2 x))

toDef :: (MClause p, Defining f) => (x -> Maybe (Match p t)) -> (x -> (t ~~ f ::: M2Ty p f))
toDef body = \x -> case body x of
  Just y  -> coerce y
  Nothing -> error "incomplete pattern coverage!"
  
class MClause m where
  type M2Ty m x
  tagM2Ty :: x -> x ::: M2Ty m x
  tagM2Ty = coerce
  
instance MClause (MName n) where
  type M2Ty (MName n) x = x == n
  
instance MClause m => MClause (MGuard g m) where
  type M2Ty (MGuard g m) x = g && M2Ty m x

instance (MClause m, MClause ms) => MClause (MCons m ms) where
  type M2Ty (MCons m ms) x = M2Ty m x || M2Ty ms x

data SomeCase t where
  SomeCase :: forall g m t. MClause (AlsoGuard (g,m)) => Match (AlsoGuard (g,m)) t -> SomeCase t
  
class Matchy f m t | f -> m where
  mkCase' :: f -> Match m t

instance Matchy (Proxy g, t ~~ n) (AlsoGuard' g (MName n)) t where
  mkCase' = coerce . snd
  
instance Matchy (Proxy g, Match m t) (AlsoGuard' g m) t where
  mkCase' = coerce . snd

data AlsoGuard' g m
unrollAlsoGuard :: Match (AlsoGuard' g m) t -> Match (AlsoGuard (g, m)) t
unrollAlsoGuard = coerce

type family AlsoGuard gms = ag | ag -> gms

type instance AlsoGuard (g, MName n)     = MGuard g (MName n)
type instance AlsoGuard (g, MGuard g' m) = MGuard g (MGuard g' m)
type instance AlsoGuard (g, MCons m ms)  = MCons (AlsoGuard (g, m)) (AlsoGuard (g, ms))

newtype Match m t = Match t
data MName n
data MGuard g m
data MCons m ms


                                                                          
{--------------------------------------------------
  Theory of equality and identity
--------------------------------------------------}

{-| `Is` (or its infix alias @~~@) is a property that is
    used to attach names within
    the proof system to Haskell values. A value of type
    @a ~~ x@ represents a concrete Haskell value of
    type @a@, along with a /name/ @x@ that can be used
    within proofs.
 
    For example, consider the following variations on
    `Data.List.sortBy` and `Data.List.mergeBy`:

@
sortBy :: ((a -> a -> Ordering) ~~ o)
       -> ([a] ~~ xs)
       -> ([a] ~~ SortedBy o xs)

mergeBy :: ((a -> a -> Ordering) ~~ o)
        -> ([a] ~~ SortedBy o xs)
        -> ([a] ~~ SortedBy o ys)
        -> ([a] ~~ Exists zs (SortedBy o zs))
@

    The refinement types encode the pre- and post-conditions on
    each function. For example, the signature of @mergeBy@ ensures
    that the two input lists have both been sorted using the same
    comparator as the merge will use.
-}
newtype Is a name = Is Defn

newtype a ~~ name = Named a

-- | Strip the name from a named value.
nameless :: (a ~~ name) -> a
nameless = coerce

{-| Given a value of type @a@, and a function
    that can be applied to /named/ variables of type @a@,
    apply the function to the value.
 
    You can think of this function as picking a secret name
    for the value; the type system ensures that the secret
    name will not be visible outside of the polymorphic function.
    For example, this is /not/ a way to get at a value's name:
@
using (named x) id
@

    The compiler responds with an error, /e.g./
@
    • Couldn't match type ‘t’ with ‘a ::: Is c’
        because type variable ‘c’ would escape its scope
@
-}
using :: a -> (forall name. (a ~~ name) -> t) -> t
using x k = k (coerce x)

-- | Like `using`, but with two parameters at the same time.
using2 :: a -> b -> (forall name1 name2. (a ~~ name1) -> (b ~~ name2) -> t) -> t
using2 x1 x2 k = k (coerce x1) (coerce x2)

named :: (forall name. (a ~~ name) -> t) -> a -> t
named k x = k (coerce x)

named2 :: (forall name1 name2. (a ~~ name1) -> (b ~~ name2) -> t) -> a -> b -> t
named2 k = \x1 x2 -> using2 x1 x2 k

bare :: (a ~~ n ::: p) -> a
bare = nameless . the

(&&.) :: (a ~~ n ::: p) -> (a ~~ n ::: q) -> (a ~~ n ::: p && q)
(&&.) _ = coerce

is_also :: (a ~~ n) -> (b ::: n == m) -> (a ~~ m)
is_also c _ = coerce c

is_also' :: (a ~~ n) -> (b ::: m == n) -> (a ~~ m)
is_also' c _ = coerce c

-- | The @Equals@ relation is used to express equality between two entities.
--   Given an equality, you are then able to substitute one side of the equality
--   for the other, anywhere you please.
newtype Equals x y = Equals Defn
type x == y = x `Equals` y
infix 4 ==
  
instance Reflexive   Equals
instance Symmetric   Equals
instance Transitive  Equals

instance Argument (Equals x y) 0 where
  type GetArg (Equals x y) 0    = x
  type SetArg (Equals x y) 0 x' = Equals x' y

instance Argument (Equals x y) 1 where
  type GetArg (Equals x y) 1    = y
  type SetArg (Equals x y) 1 y' = Equals x y'
  
-- | @x /= y@ is a convenient alias for @Not (x `Equals` y)@.
type x /= y = Not (x == y)
infix 4 /=

class c t => Lawful c t

instance Lawful Eq Int
instance Lawful Eq a => Lawful Eq [a]

same :: Lawful Eq a => (a ~~ x) -> (a ~~ y) -> Maybe (a ~~ x ::: x == y)
same x y = if nameless x == nameless y
             then Just (coerce x)
             else Nothing

-- | Given a function and an equality over ones of its arguments,
--   replace the left-hand side of the equality with the right-hand side.
substitute :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> f -> SetArg f n x'
substitute _ _ = unsafeCoerce

-- | Substitute @x'@ for @x@ under the function @f@, on the left-hand side
--   of an equality.
substituteL :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> (f == g) -> Proof (SetArg f n x' == g)
substituteL _ _ _ = QED

-- | Substitute @x'@ for @x@ under the function @f@, on the right-hand side
--   of an equality.
substituteR :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> (g == f) -> Proof (g == SetArg f n x')
substituteR _ _ _ = QED

-- | Apply a function to both sides of an equality.
apply :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> Proof (f == SetArg f n x')
apply _ _ = QED
  

{--------------------------------------------------
  Defining your own theories
--------------------------------------------------}

type Defining p = (Coercible p Defn, Coercible Defn p)

by_defn :: forall p q. (Defining p, Defining q) => p -> q
by_defn = from_defn . to_defn
  where
    to_defn   = coerce :: p -> Defn
    from_defn = coerce :: Defn -> q
    
data Defn = Defn

assert :: Defining (p t) => a -> (a ::: p t)
assert = coerce

assertNot :: Defining (p t) => a -> (a ::: Not (p t))
assertNot = coerce

assert_ex :: Defining (p t) => a -> (a ::: Exists t (p t))
assert_ex = coerce

assert_is :: Defining p => a -> (a ~~ p)
assert_is = coerce

assert_is1 :: Defining (p t) => a -> (a ~~ p t)
assert_is1 = coerce

assert_is2 :: Defining (p t t') => a -> (a ~~ p t t')
assert_is2 = coerce

assert2 :: Defining (p t t') => a -> (a ::: p t t')
assert2 = coerce

assertNot2 :: Defining (p t t') => a -> (a ~~ Not (p t t'))
assertNot2 = coerce

decompose1 :: Defining (p t) => (a -> b) -> (a ~~ p t) -> (b ~~ t)
decompose1 f x = coerce (f (coerce x))

decompose2 :: Defining (p t t') => (a -> (b, c)) -> (a ~~ p t t') -> (b ~~ t, c ~~ t')
decompose2 f x = let (x1,x2) = f (coerce x) in (coerce x1, coerce x2)

qed :: Defining (p t) => Proof (p t)
qed = QED

qed2 :: Defining (p t t') => Proof (p t t')
qed2 = QED

qedNot :: Defining (p t) => Proof (Not (p t))
qedNot = QED

qedNot2 :: Defining (p t t') => Proof (Not (p t t'))
qedNot2 = QED

assertEq :: (Defining x, Defining y) => a -> (a ::: (x == y))
assertEq = coerce

assertNotEq :: (Defining x, Defining y) => a -> (a ::: (x /= y))
assertNotEq = coerce

qedEq :: (Defining x, Defining y) => Proof (x == y)
qedEq = QED

qedNotEq :: (Defining x, Defining y) => Proof (x /= y)
qedNotEq = QED

qedEq'0 :: (Defining c) => Proof (x == c)
qedEq'0 = QED

qedEq'1 :: (Defining (c p)) => Proof (x == c p)
qedEq'1 = QED

qedEq'2 :: (Defining (c p p')) => Proof (x == c p p')
qedEq'2 = QED

guard0 :: Defining f
       => (t ::: p)
       -> (t ::: x == f && p)
guard0 = coerce

guard1 :: Defining (f (a1 x))
       => (t ::: p)
       -> (t ::: x == f (a1 x) && p)
guard1 = coerce

guard2 :: Defining (f (a1 x) (a2 x))
       => (t ::: p)
       -> (t ::: x == f (a1 x) (a2 x) && p)
guard2 = coerce

defining
  :: Defining (f x)
  => ((a ~~ x) -> b)
  -> (a ~~ x)
  -> (b ~~ f x)

defining f x = coerce (f x)

defining2
  :: Defining (f x y)
  => ((a ~~ x) -> (b ~~ y) -> c)
  -> (a ~~ x)
  -> (b ~~ y)
  -> (c ~~ f x y)

defining2 f x y = coerce (f x y)

defining2'
  :: Defining (f x y)
  => (a -> b -> c)
  -> (a ~~ x)
  -> (b ~~ y)
  -> (c ~~ f x y)

defining2' f x y = coerce (f (nameless x) (nameless y))

assert_decomp0
  :: Defining f
  => (() ::: x == f)
assert_decomp0 = coerce ()

assert_decomp1
  :: Defining (f (a1 x))
  => (() ::: x == f (a1 x))
assert_decomp1 = coerce ()

assert_decomp2
  :: Defining (f (a1 x) (a2 x))
  => (() ::: x == f (a1 x) (a2 x))
assert_decomp2 = coerce ()

-----------------------------------------------------

class Exist p where
  exists :: a -> (forall x. (a ::: p x) -> t) -> t
  exists x k = k (coerce x)


data family ForAll' :: * -> (* -> *) -> *

data family HasType :: * -> * -> *

data UserType

univ_qed' :: Coercible n UserType => Proof (ForAll' n p)
univ_qed' = QED

univ_elim' :: ForAll' n p -> x `HasType` n -> p x
univ_elim' = error "todo"

{-
newtype Of f x = Of Defn
type f $ x = f `Of` x

ap :: (a -> b) ::: Is f
   -> a       ::: Is x
   -> b       ::: Is (f $ x)
ap f x = assert (the f $ the x)

($.) :: (a -> b) ::: Is f
   -> a       ::: Is x
   -> b       ::: Is (f $ x)
($.) = ap
-}
-----------------------------------------------------
