{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.The (The(..)) where

import Data.Coerce

class The d a | d -> a where
  the :: d -> a
  default the :: Coercible d a => d -> a
  the = coerce
