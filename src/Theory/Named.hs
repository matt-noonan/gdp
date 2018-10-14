{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}

{-|
  Module      :  Theory.Named
  Copyright   :  (c) Matt Noonan 2018
  License     :  BSD-style
  Maintainer  :  matt.noonan@gmail.com
  Portability :  portable
-}

module Theory.Named
  ( -- * Named values
    Named, type (~~)
  , name
  , name2, name3

  -- ** Definitions
  , Defining
  , Defn
  , defn
  ) where

import Data.The
import Data.Coerce

{--------------------------------------------------
  Named values
--------------------------------------------------}

-- | A value of type @a ~~ name@ has the same runtime
--   representation as a value of type @a@, with a
--   phantom "name" attached.
newtype Named name a = Named a

-- | An infix alias for 'Named'.
type a ~~ name = Named name a

instance The (Named name a) a

-- | Introduce a name for the argument, and pass the
--   named argument into the given function.
name :: a -> (forall name. a ~~ name -> t) -> t
name x k = k (coerce x)

-- | Same as 'name', but names two values at once.
name2 :: a -> b -> (forall name1 name2. (a ~~ name1) -> (b ~~ name2) -> t) -> t
name2 x y k = k (coerce x) (coerce y)

-- | Same as 'name', but names three values at once.
name3 :: a -> b -> c -> (forall name1 name2 name3. (a ~~ name1) -> (b ~~ name2) -> (c ~~ name3) -> t) -> t
name3 x y z k = k (coerce x) (coerce y) (coerce z)


{--------------------------------------------------
  Definitions
--------------------------------------------------}

{-| Library authors can introduce new names in a controlled way
    by creating @newtype@ wrappers of @Defn@. The constructor of
    the @newtype@ should *not* be exported, so that the library
    can retain control of how the name is introduced.

@
newtype Bob = Bob Defn

bob :: Int ~~ Bob
bob = defn 42
@
-}
data Defn = Defn

-- | The @Defining P@ constraint holds in any module where @P@
--   has been defined as a @newtype@ wrapper of @Defn@. It
--   holds /only/ in that module, if the constructor of @P@
--   is not exported.
type Defining p = (Coercible p Defn, Coercible Defn p)

-- | In the module where the name @f@ is defined, attach the
--   name @f@ to a value.
defn :: Defining f => a -> (a ~~ f)
defn = coerce
