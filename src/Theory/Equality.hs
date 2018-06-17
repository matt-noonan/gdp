{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleContexts      #-}

module Theory.Equality
  ( -- * Theory of equality
    Equals, type (==)
  , same
  , substitute
  , substituteL
  , substituteR
  , apply

  ) where

import Data.Arguments
import Data.The
import Theory.Named
import Logic.Proof (Proof, axiom)

import Lawful

{--------------------------------------------------
  Theory of equality
--------------------------------------------------}

-- | The @Equals@ relation is used to express equality between two entities.
--   Given an equality, you are then able to substitute one side of the equality
--   for the other, anywhere you please.
newtype Equals x y = Equals Defn

type x == y = x `Equals` y
infix 4 ==

instance Argument (Equals x y) 0 where
  type GetArg (Equals x y) 0    = x
  type SetArg (Equals x y) 0 x' = Equals x' y

instance Argument (Equals x y) 1 where
  type GetArg (Equals x y) 1    = y
  type SetArg (Equals x y) 1 y' = Equals x y'

-- | Test if the two name arguments are equal an, if so, produce a proof
--   of equality for the names.
same :: Lawful Eq a => (a ~~ x) -> (a ~~ y) -> Maybe (Proof (x == y))
same x y = if the x == the y then Just axiom else Nothing

-- | Apply a function to both sides of an equality.
apply :: forall f n x x'. (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> Proof (f == SetArg f n x')
apply _ _ = axiom

-- | Given a formula and an equality over ones of its arguments,
--   replace the left-hand side of the equality with the right-hand side.
substitute :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> f -> Proof (SetArg f n x')
substitute _ _ _ = axiom

-- | Substitute @x'@ for @x@ under the function @f@, on the left-hand side
--   of an equality.
substituteL :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> (f == g) -> Proof (SetArg f n x' == g)
substituteL _ _ _ = axiom

-- | Substitute @x'@ for @x@ under the function @f@, on the right-hand side
--   of an equality.
substituteR :: (Argument f n, GetArg f n ~ x)
    => Arg n -> (x == x') -> (g == f) -> Proof (g == SetArg f n x')
substituteR _ _ _ = axiom
