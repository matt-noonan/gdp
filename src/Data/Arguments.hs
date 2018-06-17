{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}

{-|
  Module      :  Data.Arguments
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Data.Arguments
  ( Argument(..)
  , LHS, RHS
  , Arg(..)
  , arg
  ) where

-- | Get or modify a type within a larger type.
--   This is entirely a type-level operation, there
--   is nothing corresponding to a value access or update.
class Argument (f :: k1) (n :: k2) where
  type GetArg f n   :: k1
  type SetArg f n x :: k1

-- | Position: the left-hand side of a type.
data LHS

-- | Position: the right-hand side of a type.
data RHS

instance Argument (Either a b) LHS where
  type GetArg (Either a b) LHS    = a
  type SetArg (Either a b) LHS a' = Either a' b

instance Argument (Either a b) RHS where
  type GetArg (Either a b) RHS    = b
  type SetArg (Either a b) RHS b' = Either a b'

-- | A specialized proxy for arguments.
data Arg n = Arg

-- | Inhabitant of the argument proxy.
arg :: Arg n
arg = Arg

