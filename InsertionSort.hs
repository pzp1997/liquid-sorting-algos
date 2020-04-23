module InsertionSort where

import qualified Language.Haskell.Liquid.Bag as B

{-@ type IncrList a = [a]<{\x y -> x <= y}> @-}

{-@ measure listElts @-}
listElts :: Ord a => [a] -> B.Bag a
listElts [] = B.empty
listElts (x:xs) = B.put x (listElts xs)

{-@ sort :: xs:[a] -> {v:IncrList a | listElts xs = listElts v} @-}
sort [] = []
sort (x:xs) = insert x (sort xs)

{-@ insert :: x:a -> xs:IncrList a -> {v:IncrList a | listElts v = B.put x (listElts xs)} @-}
insert p [] = [p]
insert p (x:xs)
  | p <= x = p:x:xs
  | otherwise = x:insert p xs
