-- Counting-based bottom-up non-tail-recursive mergesorts
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellNTRCount where

import Data.Bits

sortN :: (a -> a -> Ordering) -> [a] -> [a]
sortN cmp = sortRec (0 :: Int) [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | cmp x y == GT = y : merge xs ys'
    | otherwise     = x : merge xs' ys

  push xs k stack | testBit k 0 =
    let ys : stack' = stack in
    let !xys = merge ys xs in
    let !k' = shift k (- 1) in push xys k' stack'
  push xs k stack = xs : stack

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec k stack (x : y : s) =
    if cmp x y /= GT then ascending (x :) y s else descending [x] y s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | cmp x y /= GT =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | cmp x y == GT = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s = pop s stack

sort3N :: (a -> a -> Ordering) -> [a] -> [a]
sort3N cmp = sortRec (0 :: Int) [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | cmp x y == GT = y : merge xs ys'
    | otherwise     = x : merge xs' ys

  push xs k stack | testBit k 0 =
    let ys : stack' = stack in
    let !xys = merge ys xs in
    let !k' = shift k (- 1) in push xys k' stack'
  push xs k stack = xs : stack

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec k stack (x : y : z : s)
    | cmp x y /= GT, cmp y z /= GT = ascending (\s -> x : y : s) z s
    | cmp x y == GT, cmp y z == GT = descending [y, x] z s
    | cmp x y /= GT, cmp y z == GT =
      let !k' = k + 1 in
      let !xyz = if cmp x z /= GT then [x, z, y] else [z, x, y] in
      let !stack' = push xyz k stack in sortRec k' stack' s
    | cmp x y == GT, cmp y z /= GT =
      let !k' = k + 1 in
      let !xyz = if cmp x z /= GT then [y, x, z] else [y, z, x] in
      let !stack' = push xyz k stack in sortRec k' stack' s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | cmp x y /= GT =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | cmp x y == GT = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if cmp x y /= GT then s else [y, x] in pop xy stack
  sortRec k stack s = pop s stack
