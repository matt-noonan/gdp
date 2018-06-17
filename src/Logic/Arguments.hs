{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}

module Logic.Arguments
  ( Arg(..)
  , arg
  , Argument(..)
  ) where

import GHC.TypeLits

data Arg n = Arg

arg :: Arg n
arg = Arg

class Argument (f :: k1) (n :: k2) where
  type GetArg f n   :: k1
  type SetArg f n x :: k1

{-
-- 1-argument functions
instance Argument (f (x :: *)) 0 where
  type GetArg (f x) 0    = x
  type SetArg (f x) 0 x' = f x'

-- 2-argument functions
instance Argument (f (x :: *) (y :: *)) 0 where
  type GetArg (f x y) 0    = x
  type SetArg (f x y) 0 x' = f x' y

instance Argument (f (x :: *) (y :: *)) 1 where
  type GetArg (f x y) 1    = x
  type SetArg (f x y) 1 y' = f x y'

-- 3-argument functions
instance Argument (f (x :: *) (y :: *) (z :: *)) 0 where
  type GetArg (f x y z) 0    = x
  type SetArg (f x y z) 0 x' = f x' y z

instance Argument (f (x :: *) (y :: *) (z :: *)) 1 where
  type GetArg (f x y z) 1    = y
  type SetArg (f x y z) 1 y' = f x y' z

instance Argument (f (x :: *) (y :: *) (z :: *)) 2 where
  type GetArg (f x y z) 2    = z
  type SetArg (f x y z) 2 z' = f x y z'
-}
