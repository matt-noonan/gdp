{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DefaultSignatures      #-}

module Tactics
  ( Simplifiable (..)
  ) where

import Data.Coerce

class Simplifiable p p' | p -> p' where
  simplify :: p -> p'
  -- default simplify :: Coercible p p' => p -> p'
  simplify = error "todo" -- coerce
