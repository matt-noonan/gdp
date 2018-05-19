{-# LANGUAGE TypeOperators #-}

module Theory.Nat.Derived
  ( zero_neutralR
  , (-!)
  ) where

import Logic.Propositional
import Theory.Nat.Assumed


zero_neutralR :: Proof (n == n + Zero)
zero_neutralR = do
  eq1 <- zero_neutralL
  eq2 <- commutative
  transitive eq1 eq2


newtype ClampedDiff n m = ClampedDiff Defn
type x -! y = ClampedDiff x y

-- | Subtraction with a clamp at zero
(-!) :: (Integer ~~ n)
     -> (Integer ~~ m)
     -> (Integer ~~ (n -! m) :::
        ( ((n < m) && (n -! m) == Zero)
        || (n == m + (n -! m) )))

x -! y = error "sorry"

infixl 6 -!
