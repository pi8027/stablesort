-- Stack-based bottom-up non-tail-recursive mergesorts
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellNTRStack where

import Data.Bits

sort3 :: (a -> a -> Bool) -> [a] -> [a]
sort3 (<=) = sortRec (0 :: Int) [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | x <= y    = x : merge xs' ys
    | otherwise = y : merge xs ys'

  push xs k stack | testBit k 0 =
    let ys : stack' = stack in
    let !xys = merge ys xs in
    let !k' = shift k (- 1) in push xys k' stack'
  push xs k stack = xs : stack

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec k stack (x : y : z : s) =
    let !xyz = if x <= y then
                 if y <= z then [x, y, z]
                 else if x <= z then [x, z, y] else [z, x, y]
               else
                 if x <= z then [y, x, z]
                 else if y <= z then [y, z, x] else [z, y, x]
    in
    let !k' = k + 1 in
    let !stack' = push xyz k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if x <= y then s else [y, x] in pop xy stack
  sortRec k stack s = pop s stack

sortN :: (a -> a -> Bool) -> [a] -> [a]
sortN (<=) = sortRec (0 :: Int) [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | x <= y    = x : merge xs' ys
    | otherwise = y : merge xs ys'

  push xs k stack | testBit k 0 =
    let ys : stack' = stack in
    let !xys = merge ys xs in
    let !k' = shift k (- 1) in push xys k' stack'
  push xs k stack = xs : stack

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec k stack (x : y : s) =
    if x <= y then ascending (x :) y s else descending [x] y s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | x <= y =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | not (x <= y) = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s = pop s stack

sort3N :: (a -> a -> Bool) -> [a] -> [a]
sort3N (<=) = sortRec (0 :: Int) [] where
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x : xs') ys@(y : ys')
    | x <= y    = x : merge xs' ys
    | otherwise = y : merge xs ys'

  push xs k stack | testBit k 0 =
    let ys : stack' = stack in
    let !xys = merge ys xs in
    let !k' = shift k (- 1) in push xys k' stack'
  push xs k stack = xs : stack

  pop xs [] = xs
  pop xs (ys : stack) = let !xys = merge ys xs in pop xys stack

  sortRec k stack (x : y : z : s)
    | x <= y,       y <= z       = ascending (\s -> x : y : s) z s
    | not (x <= y), not (y <= z) = descending [y, x] z s
    | x <= y,       not (y <= z) =
      let !k' = k + 1 in
      let !xyz = if x <= z then [x, z, y] else [z, x, y] in
      let !stack' = push xyz k stack in sortRec k' stack' s
    | not (x <= y), y <= z =
      let !k' = k + 1 in
      let !xyz = if x <= z then [y, x, z] else [y, z, x] in
      let !stack' = push xyz k stack in sortRec k' stack' s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | x <= y =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | not (x <= y) = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if x <= y then s else [y, x] in pop xy stack
  sortRec k stack s = pop s stack
