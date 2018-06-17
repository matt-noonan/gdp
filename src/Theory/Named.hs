{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Theory.Named
  ( -- * Named values
    Named, type (~~)
  , name, (~~)
  , name2
  , name3

  -- ** Definitions
  , Defining
  , Defn
  , defn
  ) where

import The
import Data.Coerce

{--------------------------------------------------
  Named values
--------------------------------------------------}

newtype Named name a = Named a

type a ~~ name = Named name a

instance The (Named name a) a

name :: a -> (forall name. a ~~ name -> t) -> t
name x k = k (coerce x)

(~~) :: a -> (forall name. a ~~ name -> t) -> t
(~~) = name

name2 :: a -> b -> (forall name1 name2. (a ~~ name1) -> (b ~~ name2) -> t) -> t
name2 x y k = k (coerce x) (coerce y)

name3 :: a -> b -> c -> (forall name1 name2 name3. (a ~~ name1) -> (b ~~ name2) -> (c ~~ name3) -> t) -> t
name3 x y z k = k (coerce x) (coerce y) (coerce z)


{--------------------------------------------------
  Definitions
--------------------------------------------------}

type Defining p = (Coercible p Defn, Coercible Defn p)

data Defn = Defn

defn :: Defining f => a -> (a ~~ f)
defn = coerce
