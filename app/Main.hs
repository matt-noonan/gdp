{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs         #-}

module Main where

import GDP

import Data.Ord
import qualified Data.List as L

-- An unsafe merge. This relies on the user remembering to
-- sort both of the inputs using the same comparator passed
-- as the first argument to `unsafeMergeBy`. Otherwise, it
-- will produce nonsense.
unsafeMergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
unsafeMergeBy comp xs ys = go xs ys
  where
    go [] ys' = ys'
    go xs' [] = xs'
    go (x:xs') (y:ys') = case comp x y of
      GT -> y : go (x:xs') ys'
      _  -> x : go xs' (y:ys')


-- Introduce a predicate `SortedBy comp`, indicating that
-- the value has been sorted by the comparator named `comp`.
newtype SortedBy comp name = SortedBy Defn

-- Sort a value using the comparator named `comp`. The
-- resulting value will satisfy `SortedBy comp`.
sortBy :: ((a -> a -> Ordering) ~~ comp)
       -> [a]
       -> ([a] ?SortedBy comp)
sortBy comp xs = assert (L.sortBy (the comp) xs)

-- Merge the two lists using the comparator named `comp`. The lists must
-- have already been sorted using `comp`, and the result will also be
-- sorted with respect to `comp`.
mergeBy :: ((a -> a -> Ordering) ~~ comp)
        -> ([a] ?SortedBy comp)
        -> ([a] ?SortedBy comp)
        -> ([a] ?SortedBy comp)
mergeBy comp xs ys = assert (unsafeMergeBy (the comp) (the xs) (the ys))

newtype Opposite comp = Opposite Defn

-- A named version of the opposite ordering.
opposite :: ((a -> a -> Ordering) ~~ comp)
         -> ((a -> a -> Ordering) ~~ Opposite comp)
opposite comp = defn $ \x y -> case (the comp) x y of
  GT -> LT
  EQ -> EQ
  LT -> GT

newtype Reverse xs = Reverse Defn

-- A named version of Prelude's 'reverse'.
rev :: ([a] ~~ xs) -> ([a] ~~ Reverse xs)
rev xs = defn (reverse (the xs))

-- A lemma about reversing sorted lists.
rev_ord_lemma :: SortedBy comp xs -> Proof (SortedBy (Opposite comp) (Reverse xs))
rev_ord_lemma _ = axiom

-- Usage example.
main :: IO ()
main = do
  name compare $ \up -> do

    -- Read two lists and sort them in ascending order, then
    -- merge them and print the result.
    xs <- sortBy up <$> (readLn :: IO [Int])
    ys <- sortBy up <$> readLn
    let ans1 = mergeBy up xs ys
    print (the ans1)

    -- Now reverse the two lists and merge them using the
    -- descending comparator. This requires a proof that
    -- the reversed lists are sorted by the opposite of `up`,
    -- which we provide using (...?).
    let down = opposite up
        ans2 = mergeBy down (rev' xs) (rev' ys)
        rev' = rev ...? rev_ord_lemma
    print (the ans2)
