{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Tutorial.Hillel where

import Logic.Propositional
import Theory.Lists
import Theory.Nat

{-| Left Pad

type Hillel_leftpad_spec n c xs
  -- Two cases: when the list length is less than the desired
  --            case, or when it is longer that the desired length.
   = (Length xs < n      && Hillel_leftpad_spec_normal (n -! Length xs) n c xs)
  || (Not (Length xs < n) && Hillel_leftpad_spec_longlist n c xs)


type Hillel_leftpad_spec_normal k n c xs
  -- The "normal" case: the result should be k repetitions of c,
  -- followed by xs.
  =  Take k (Leftpad n c xs) == Replicate k c
  && Drop k (Leftpad n c xs) == xs
  && k + Length xs == n

type Hillel_leftpad_spec_longlist n c xs
  = Leftpad n c xs == xs

leftpad_verified :: (Integer ~~ n)
                 -> (Char ~~ c)
                 -> (String ~~ xs)
                 -> (String ~~ LeftPad n c xs ::: Hillel_leftpad_spec n c xs)
leftpad_verified _ _ _ = error "todo"
-}
