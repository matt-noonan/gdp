{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}

module Theory.Nat.Assumed
  ( Nat
  , Zero
  , Succ
  , Pred
  , IsZero
  , IsSucc
  
  , zero
  , one
  , succ
  , pred
  , Plus
  , type (+)

  -- * Peano axioms
  , zero_not_succ
  , succ_inj
  , zero_neutralL
  , succ_add
  , zero_absorbL
  , succ_add_mul
  , induction

  -- * Ordering axioms
  , type (<)
  , trichotomy
  , order_addL
  , order_mulL
  , exists_diff
  , zero_then_one
  , zero_min

  , compare_eq
  , induct
  , compare_tri

  , zero_case
  , succ_case

  , nat_cases
  , def_by_nat_cases

  ) where

import Prelude hiding (succ, pred)
import Logic.Propositional
import Data.Proxy

-- | The natural numbers
newtype Nat = Nat Defn

-- | @IsNat@ is a predicate that defines membership in the natural numbers.
newtype IsNat n = IsNat Defn

instance Argument (IsNat n) 0 where
  type GetArg (IsNat n) 0    = n
  type SetArg (IsNat n) 0 n' = IsNat n'
  
-- | Zero
newtype Zero = Zero Defn

-- | The successor operation
newtype Succ n = Succ Defn

instance Argument (Succ n) 0 where
  type GetArg (Succ n) 0    = n
  type SetArg (Succ n) 0 n' = Succ n'

-- | Is this natural number zero?
newtype IsZero n = IsZero Defn

instance Argument (IsZero n) 0 where
  type GetArg (IsZero n) 0    = n
  type SetArg (IsZero n) 0 n' = IsZero n'

-- | Is this natural number a successor?
newtype IsSucc n = IsSucc Defn

instance Argument (IsSucc n) 0 where
  type GetArg (IsSucc n) 0    = n
  type SetArg (IsSucc n) 0 n' = IsSucc n'

instance Cases (IsZero n) ((IsZero n && p) || (IsSucc n && q)) p where
  cases _ _ = sorry

instance Cases Zero ((IsZero Zero && p) || (IsSucc Zero && q)) p where
  cases _ _ = sorry

instance Cases (IsSucc n) ((IsZero n && p) || (IsSucc n && q)) q where
  cases _ _ = sorry
  
instance Cases (Succ n) ((IsZero (Succ n) && p) || (IsSucc (Succ n) && q)) q where
  cases _ _ = sorry
  
-- | Addition of natural numbers.
newtype Plus x y = Plus Defn
type x + y = x `Plus` y
infixl 6 +
  
instance Commutative Plus
instance Associative Plus

instance Argument (Plus x y) 0 where
  type GetArg (Plus x y) 0    = x
  type SetArg (Plus x y) 0 x' = Plus x' y
  
instance Argument (Plus x y) 1 where
  type GetArg (Plus x y) 1    = y
  type SetArg (Plus x y) 1 y' = Plus x y'
  
-- | Multiplication of natural numbers.
newtype Times x y = Times Defn
type x * y = x `Times` y
infixl 7 *
  
instance Commutative Times
instance Associative Times

instance Distributive Times Plus

instance Argument (Times x y) 0 where
  type GetArg (Times x y) 0    = x
  type SetArg (Times x y) 0 x' = Times x' y
  
instance Argument (Times x y) 1 where
  type GetArg (Times x y) 1    = y
  type SetArg (Times x y) 1 y' = Times x y'
 
{-| Proof by induction.
-}
induction :: (Argument p a)
         => Proof (SetArg p a Zero)                -- ^ The base case
         -> (forall n. (SetArg p a n) -> Proof (SetArg p a (Succ n)))  -- ^ Inductive case
         -> IsNat m -> Proof (SetArg p a m)
induction _ _ _ = sorry

-- | Zero.
zero :: Integer ~~ Zero
zero = assert_is 0

-- | One.
one :: Integer ~~ Succ Zero
one = assert_is 1

-- | The successor function.
succ :: (Integer ~~ n) -> (Integer ~~ Succ n)
succ n = assert_is (nameless n + 1)

-- | Zero is not the successor of any natural number.
zero_not_succ :: Proof (Zero /= Succ n)
zero_not_succ = qedNotEq

-- | The successor function is injective.
succ_inj :: (Succ m == Succ n) -> Proof (m == n)
succ_inj _ = sorry

-- | Zero is neutral for addition on the left.
zero_neutralL :: Proof (n == Zero + n)
zero_neutralL = qedEq'0

-- | The successor interacts with addition.
succ_add :: Proof (n + Succ m == Succ (n + m))
succ_add = qedEq

-- | Zero is absorbing for multiplication on the left.
zero_absorbL :: Proof (Zero == Zero * n)
zero_absorbL = sorry

-- | A axiom relating addition, multiplication, and the successor operation.
succ_add_mul :: Proof (m * Succ n == m * n + m)
succ_add_mul = sorry

{-------------------------------------------------------
  Facts about the ordering on the natural numbers
-------------------------------------------------------}

newtype LessThan x y = LessThan Defn

instance Argument (LessThan x y) 0 where
  type GetArg (LessThan x y) 0    = x
  type SetArg (LessThan x y) 0 x' = LessThan x' y
  
instance Argument (LessThan x y) 1 where
  type GetArg (LessThan x y) 1    = y
  type SetArg (LessThan x y) 1 y' = LessThan x y'

type x < y = LessThan x y
infix 4 <

instance Transitive    LessThan
instance Antisymmetric LessThan
instance Irreflexive   LessThan

trichotomy :: Proof (x < y || x == y || y < x)
trichotomy = sorry

order_addL :: (x < y) -> Proof (z + x < z + y)
order_addL _ = sorry

order_mulL :: (z /= Zero) -> (x < y) -> Proof (z * x < z * y)
order_mulL _ _ = sorry

-- | If x is less than
exists_diff :: (x < y) -> Proof (Exists z (x + z == y))
exists_diff _ = sorry

-- | There are no numbers between zero and one.
zero_then_one :: (Zero < x) -> Proof (x == Succ Zero || Succ Zero < x)
zero_then_one _ = sorry

-- | Zero is the smallest natural number.
zero_min :: Proof (x == Zero || Zero < x)
zero_min = sorry

-- | Compare @x@ to @y@ and execute the corresponding case,
--   while providing evidence that @x == y@ or @x /= y@ as appropriate.
compare_eq :: (Integer ~~ x)
          -> (Integer ~~ y)
          -> (Proof (x == y) -> t)
          -> (Proof (x /= y) -> t)
          -> t
compare_eq x y t f = case nameless x == nameless y of
  True  -> t sorry
  False -> f sorry

newtype Pred n = Pred Defn

instance Argument (Pred n) 0 where
  type GetArg (Pred n) 0    = n
  type SetArg (Pred n) 0 n' = Pred n'
  
pred :: (Integer ~~ x ::: x /= Zero)
    -> (Integer ~~ Pred x ::: x == Succ (Pred x))
pred x = inject sorry $ assert_is (bare x - 1)

induct :: (Integer ~~ x)
      -> (Proof (x == Zero) -> t)
      -> (Proof (x == Succ (Pred x)) -> (Integer ~~ Pred x) -> t)
      -> t
induct x z s = if nameless x == 0
               then z sorry
               else s sorry (assert_is $ nameless x - 1)

-- | Compare @x@ to @y@ and execute the corresponding case,
--   while providing evidence that @x < y@, @x == y@, or @y < x@
--   as appropriate.
compare_tri :: (Integer ~~ x)
           -> (Integer ~~ y)
           -> (Proof (x < y) -> t)
           -> (Proof (x == y) -> t)
           -> (Proof (y < x) -> t)
           -> t
compare_tri x y lt eq gt =
  case compare (nameless x) (nameless y) of
    LT -> lt sorry
    EQ -> eq sorry
    GT -> gt sorry

zero_case :: IsZero n -> ((n == Zero) -> Proof t) -> Proof t
zero_case  _ f = do
  zeq <- sorry
  f zeq

succ_case :: IsSucc n -> ((n == Succ (Pred n)) -> Proof t) -> Proof t
succ_case _ f = do
  speq <- sorry
  f speq

-- | Define a value by pattern matching on a natural number.
nat_cases :: (Integer ~~ n)
         -> (Proof (IsZero n) -> t)
         -> (Proof (IsSucc n) -> (Integer ~~ Pred n) -> t)
         -> t
nat_cases n zc sc =
  case nameless n of
    0 -> zc sorry
    m -> sc sorry (assert_is (m - 1))

-- | Define a named function by pattern-matching on a natural number.
def_by_nat_cases :: (Defining f, Argument f a, GetArg f a ~ n)
  => Arg a
  -> (Integer ~~ n)
  -> (Proof (IsZero n) -> (t ~~ zcase))
  -> (Proof (IsSucc n) -> (Integer ~~ Pred n) -> (t ~~ scase))
  -> (t ~~ f ::: ((IsZero n && (f == zcase))
              || (IsSucc n && (f == scase))))
def_by_nat_cases _ n zc sc = inject sorry $
  assert_is $ nat_cases n (nameless.zc) (\pf p -> nameless (sc pf p))

nat_cases' :: forall n f a zcase scase t1 t2 t m1 m2. (Defining f, Argument f a, GetArg f a ~ n,
                                                     Matchy (Proxy (IsZero n), t1) m1 t, Matchy (Proxy (IsSucc n), t2) m2 t)
  => (Proof (IsZero n) -> t1) 
  -> (Proof (IsSucc n) -> (Integer ~~ Pred n) -> t2)
  -> (Integer ~~ n)
  -> Maybe (Match (MCons (AlsoGuard (IsZero n, m1))
                         (AlsoGuard (IsSucc n, m2))) t)

nat_cases' zc sc
  =   defCase (Proxy @(IsZero n)) ((== 0) . nameless) (const $ zc sorry)
  <+> defCase (Proxy @(IsSucc n)) ((/= 0) . nameless) (\n -> sc sorry (assert_is $ nameless n - 1))
