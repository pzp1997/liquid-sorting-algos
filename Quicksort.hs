module Sort where

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
sort l@(x:xs) =
  let (lts, gts) = partition x xs in
  combine x (sort lts) (sort gts)

{-@ partition :: p:a -> xs:[a] -> {v:([{x:a | x < p}], [{x:a | x >= p}]) | listElts xs = B.union (listElts (fst v)) (listElts (snd v)) && len xs == len (fst v) + len (snd v)} @-}
(x::Int, {v:Int | x <= v})
partition p [] = ([], [])
partition p (x:xs) =
  let (lts, gts) = partition p xs in
  if x < p then (x:lts, gts)
  else (lts, x:gts)

{-@ combine :: p:a -> lts:(IncrList {x:a | x < p}) -> gts:(IncrList {x:a | x >= p}) -> {v:IncrList a | listElts v = B.union (listElts lts) (B.put p (listElts gts))} @-}
combine p [] gts = p:gts
combine p (lt:lts) gts = lt : combine p lts gts
