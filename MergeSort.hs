module InsertionSort where

import qualified Language.Haskell.Liquid.Bag as B

{-@ type IncrList a = [a]<{\x y -> x <= y}> @-}

{-@ measure listElts @-}
listElts :: Ord a => [a] -> B.Bag a
listElts [] = B.empty
listElts (x:xs) = B.put x (listElts xs)

{-@ measure fst @-}
fst :: (a, b) -> a
fst (x, _) = x

{-@ measure snd @-}
snd :: (a, b) -> b
snd (_, y) = y

{-@ sort :: xs:[a] -> {v:IncrList a | listElts xs = listElts v} @-}
sort [] = []
sort [x] = [x]
sort l =
  let (xs, ys) = split l in
  merge (sort xs) (sort ys)

{-@ split :: {xs:[a] | len xs >= 2} -> {v:([a], [a]) | listElts xs = B.union (listElts (fst v)) (listElts (snd v)) && len (fst v) + len (snd v) = len xs && len (fst v) - len (snd v) <= 1 && len (fst v) < len xs && len (snd v) < len xs} @-}
split [x, y] = ([x], [y])
split [x, y, z] = ([x, z], [y])
split (x:y:zs) =
  let (xs, ys) = split zs in
  (x:xs, y:ys)

{-@ merge :: xs:IncrList a -> ys:IncrList a -> {v:IncrList a | listElts v = B.union (listElts xs) (listElts ys)} / [len xs + len ys] @-}
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys
