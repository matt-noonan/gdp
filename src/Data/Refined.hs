{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Refined
  (  -- * Refinement types
    (:::)
  , (...)
  , unrefined
  ) where

import Data.The
import Logic.Proof (Proof)

import Data.Coerce

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
newtype a ::: p = SuchThat a
infixr 1 :::

instance The a' a => The (a' ::: p) a where
  the (SuchThat x) = the x

-- | Given a value and a proof, attach the proof as a
--   phantom refinement on the value.
(...) :: a -> Proof p -> (a ::: p)
x ...proof = coerce x

-- | Forget the ghost proof attached to a type.
unrefined :: (a ::: p) -> a
unrefined = coerce

