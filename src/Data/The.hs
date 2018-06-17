{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ViewPatterns           #-}

{-|
  Module      :  Data.The
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Data.The
  ( The(..)
  , pattern The
  ) where

import Data.Coerce

{-| A class for extracing "the" underlying value.
    'the' should ideally be a coercion from some
    @newtype@ wrap of @a@ back to @a@.
 
    For this common use case, in the module where
    @newtype New a = New a@ is defined, an instance
    of @The@ can be created with an empty definition:

@
newtype New a = New a
instance The (New a) a
@
-}
class The d a | d -> a where
  the :: d -> a
  default the :: Coercible d a => d -> a
  the = coerce

{-| A view pattern for discarding the wrapper around
    a value.

@
f (The x) = expression x
@

    is equivalent to

@
f x = let x' = the x in expression x'
@
-}
pattern The :: The d a => a -> d
pattern The x <- (the -> x)
