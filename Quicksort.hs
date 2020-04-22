module Sort where

import qualified Language.Haskell.Liquid.Bag as B


{-@ type IncrList a = [a]<{\x y -> x <= y}> @-}

{-@ measure listElts @-}
listElts :: Ord a => [a] -> B.Bag a
listElts [] = B.empty
listElts (x:xs) = B.put x (listElts xs)

-- {-@ appendListEltsDistributiveProperty :: xs:[a] -> ys:[a] -> {listElts (xs ++ ys) = B.union (listElts xs) (listElts ys)} @-}
-- appendListEltsDistributiveProperty [] ys = ys
-- appendListEltsDistributiveProperty (x:xs) ys = appendListEltsDistributiveProperty xs ys

{-@ measure fst @-}
fst :: (a, b) -> a
fst (x, _) = x

{-@ measure snd @-}
snd :: (a, b) -> b
snd (_, y) = y

{-@ inline assert @-}
{-@ assert :: TT -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ assertListStrictUpperBound :: p:a -> [{x:a | x < p}] -> b -> b @-}
assertListStrictUpperBound :: a -> [a] -> b -> b
assertListStrictUpperBound _ _ x = x

{-@ assertListLowerBound :: p:a -> [{x:a | x >= p}] -> b -> b @-}
assertListLowerBound :: a -> [a] -> b -> b
assertListLowerBound _ _ x = x

{-@ assertSortedList :: IncrList a -> b -> b @-}
assertSortedList :: [a] -> b -> b
assertSortedList _ x = x

{-@ append :: p:a -> lts:(IncrList {x:a | x < p}) -> gts:(IncrList {x:a | x >= p}) -> {v:IncrList a | listElts v = B.union (listElts lts) (B.put p (listElts gts))} @-}
append :: a -> [a] -> [a] -> [a]
append p [] gts = p:gts
append p (lt:lts) gts = lt : append p lts gts

{-@ sort :: xs:[a] -> {v:IncrList a | listElts xs = listElts v} @-}
sort :: Ord a => [a] -> [a]
sort [] = []
sort l@(x:xs) =
    let (lts, gts) = partition x xs in
    append x (sort lts) (sort gts)
    -- assert (listElts xs == B.union (listElts lts) (listElts gts)) $
    -- assert (listElts lts == listElts (sort lts)) $
    -- assert (listElts gts == listElts (sort gts)) $
    -- let a = sort lts in
    -- let b = x : sort gts in
    -- let c = append x a b in
    -- assert (listElts l == B.union (listElts a) (listElts b)) $
    -- assertListStrictUpperBound x a $
    -- assertListLowerBound x b $
    -- assert (listElts l == listElts c) $
    -- assertSortedList a $
    -- assertSortedList b $
    -- assertSortedList c $
    -- c

{-@ partition :: p:a -> xs:[a] -> {v:([{x:a | x < p}], [{x:a | x >= p}]) | listElts xs = B.union (listElts (fst v)) (listElts (snd v)) && len xs == len (fst v) + len (snd v)} @-}
partition p [] = ([], [])
partition p (x:xs) =
    let (lts, gts) = partition p xs in
    if x < p then
        (x:lts, gts)
    else
        (lts, x:gts)
