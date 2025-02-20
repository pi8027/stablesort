-- Stack-based bottom-up non-tail-recursive mergesorts
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellNTRStack where

sort3 :: (a -> a -> Ordering) -> [a] -> [a]
sort3 cmp = sortRec [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | cmp x y == GT = y : merge xs ys'
    | otherwise     = x : merge xs' ys

  push xs [] = [xs]
  push xs ([] : stack) = xs : stack
  push xs (ys : stack) =
    let !xys = merge ys xs in
    let !stack' = push xys stack in [] : stack'

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec stack (x : y : z : s) =
    let xyz = if cmp x y /= GT then
                if cmp y z /= GT then [x, y, z]
                else if cmp x z /= GT then [x, z, y] else [z, x, y]
              else
                if cmp x z /= GT then [y, x, z]
                else if cmp y z /= GT then [y, z, x] else [z, y, x]
    in
    let !stack' = push xyz stack in sortRec stack' s
  sortRec stack s@[x, y] =
    let !xy = if cmp x y /= GT then s else [y, x] in pop xy stack
  sortRec stack s = pop s stack

sortN :: (a -> a -> Ordering) -> [a] -> [a]
sortN cmp = sortRec [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | cmp x y == GT = y : merge xs ys'
    | otherwise     = x : merge xs' ys

  push xs [] = [xs]
  push xs ([] : stack) = xs : stack
  push xs (ys : stack) =
    let !xys = merge ys xs in
    let !stack' = push xys stack in [] : stack'

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec stack (x : y : s) =
    if cmp x y /= GT then ascending (x :) y s else descending [x] y s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | cmp x y /= GT =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !xs = accu [x] in
        let !stack' = push xs stack in sortRec stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | cmp x y == GT = descending (x : accu) y s
      descending accu x s =
        let !stack' = push (x : accu) stack in sortRec stack' s
  sortRec stack s = pop s stack

sort3N :: (a -> a -> Ordering) -> [a] -> [a]
sort3N cmp = sortRec [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | cmp x y == GT = y : merge xs ys'
    | otherwise     = x : merge xs' ys

  push xs [] = [xs]
  push xs ([] : stack) = xs : stack
  push xs (ys : stack) =
    let !xys = merge ys xs in
    let !stack' = push xys stack in [] : stack'

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec stack (x : y : z : s)
    | cmp x y /= GT, cmp y z /= GT = ascending (\s -> x : y : s) z s
    | cmp x y == GT, cmp y z == GT = descending [y, x] z s
    | cmp x y /= GT, cmp y z == GT =
      let !xyz = if cmp x z /= GT then [x, z, y] else [z, x, y] in
      let !stack' = push xyz stack in sortRec stack' s
    | cmp x y == GT, cmp y z /= GT =
      let xyz = if cmp x z /= GT then [y, x, z] else [y, z, x] in
      let !stack' = push xyz stack in sortRec stack' s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | cmp x y /= GT =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !xs = accu [x] in
        let !stack' = push xs stack in sortRec stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | cmp x y == GT = descending (x : accu) y s
      descending accu x s =
        let !stack' = push (x : accu) stack in sortRec stack' s
  sortRec stack s@[x, y] =
    let !xy = if cmp x y /= GT then s else [y, x] in pop xy stack
  sortRec stack s = pop s stack
