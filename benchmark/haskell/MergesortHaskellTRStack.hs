-- Stack-based bottom-up tail-recursive mergesorts
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellTRStack where

import Data.List
import Data.Bits

catrev [] ys = ys
catrev (x : xs) ys = catrev xs (x : ys)

sort3 :: (a -> a -> Bool) -> [a] -> [a]
sort3 (<=) = sortRec (0 :: Int) [] where
  revmerge [] ys accu = catrev ys accu
  revmerge xs [] accu = catrev xs accu
  revmerge xs@(x : xs') ys@(y : ys') accu
    | x <= y    = revmerge xs' ys (x : accu)
    | otherwise = revmerge xs ys' (y : accu)

  revmergeRev [] ys accu = catrev ys accu
  revmergeRev xs [] accu = catrev xs accu
  revmergeRev xs@(x : xs') ys@(y : ys') accu
    | y <= x    = revmergeRev xs' ys (x : accu)
    | otherwise = revmergeRev xs ys' (y : accu)

  push xs k stack | even k = xs : stack
  push xs k stack
    | testBit k 1 =
      let ys : zs : stack' = stack in
      let !xys = revmerge ys xs [] in
      let !xyzs = revmergeRev xys zs [] in
      let !k' = shift k (- 2) in push xyzs k' stack'
    | otherwise =
      let ys : stack' = stack in
      let !xys = revmerge ys xs [] in xys : stack'

  pop xs k [] = xs
  pop xs k stack | odd k =
    let ys : stack' = stack in
    let !xys = revmerge ys xs [] in
    let !k' = shift k (- 1) in popRev xys k' stack'
  pop xs k stack
    | testBit k 1 =
      let !xs' = reverse xs in
      let !k' = shift k (- 1) in popRev xs' k' stack
    | otherwise = let !k' = shift k (- 2) in pop xs k' stack
  popRev xs k [] = reverse xs
  popRev xs k stack | odd k =
    let ys : stack' = stack in
    let !xys = revmergeRev xs ys [] in
    let !k' = shift k (- 1) in pop xys k' stack'
  popRev xs k stack
    | testBit k 1 =
      let !xs' = reverse xs in
      let !k' = shift k (- 1) in pop xs' k' stack
    | otherwise = let !k' = shift k (- 2) in popRev xs k' stack

  sortRec k stack (x : y : z : s) =
    let xyz = if x <= y then
                if y <= z then [x, y, z]
                else if x <= z then [x, z, y] else [z, x, y]
              else
                if x <= z then [y, x, z]
                else if y <= z then [y, z, x] else [z, y, x]
    in
    let !k' = k + 1 in
    let !stack' = push xyz k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if x <= y then s else [y, x] in pop xy k stack
  sortRec k stack s = pop s k stack

sortN :: (a -> a -> Bool) -> [a] -> [a]
sortN (<=) = sortRec (0 :: Int) [] where
  revmerge [] ys accu = catrev ys accu
  revmerge xs [] accu = catrev xs accu
  revmerge xs@(x : xs') ys@(y : ys') accu
    | x <= y    = revmerge xs' ys (x : accu)
    | otherwise = revmerge xs ys' (y : accu)

  revmergeRev [] ys accu = catrev ys accu
  revmergeRev xs [] accu = catrev xs accu
  revmergeRev xs@(x : xs') ys@(y : ys') accu
    | y <= x    = revmergeRev xs' ys (x : accu)
    | otherwise = revmergeRev xs ys' (y : accu)

  push xs k stack | even k = xs : stack
  push xs k stack
    | testBit k 1 =
      let ys : zs : stack' = stack in
      let !xys = revmerge ys xs [] in
      let !xyzs = revmergeRev xys zs [] in
      let !k' = shift k (- 2) in push xyzs k' stack'
    | otherwise =
      let ys : stack' = stack in
      let !xys = revmerge ys xs [] in xys : stack'

  pop xs k [] = xs
  pop xs k stack | odd k =
    let ys : stack' = stack in
    let !xys = revmerge ys xs [] in
    let !k' = shift k (- 1) in popRev xys k' stack'
  pop xs k stack
    | testBit k 1 =
      let !xs' = reverse xs in
      let !k' = shift k (- 1) in popRev xs' k' stack
    | otherwise = let !k' = shift k (- 2) in pop xs k' stack
  popRev xs k [] = reverse xs
  popRev xs k stack | odd k =
    let ys : stack' = stack in
    let !xys = revmergeRev xs ys [] in
    let !k' = shift k (- 1) in pop xys k' stack'
  popRev xs k stack
    | testBit k 1 =
      let !xs' = reverse xs in
      let !k' = shift k (- 1) in pop xs' k' stack
    | otherwise = let !k' = shift k (- 2) in popRev xs k' stack

  sortRec k stack (x : y : s) =
    if x <= y then ascending (x :) y s else descending [x] y s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs k stack
      ascending accu x (y : s) | x <= y =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) k stack
      descending accu x (y : s) | not (x <= y) = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s = pop s k stack

sort3N :: (a -> a -> Bool) -> [a] -> [a]
sort3N (<=) = sortRec (0 :: Int) [] where
  revmerge [] ys accu = catrev ys accu
  revmerge xs [] accu = catrev xs accu
  revmerge xs@(x : xs') ys@(y : ys') accu
    | x <= y    = revmerge xs' ys (x : accu)
    | otherwise = revmerge xs ys' (y : accu)

  revmergeRev [] ys accu = catrev ys accu
  revmergeRev xs [] accu = catrev xs accu
  revmergeRev xs@(x : xs') ys@(y : ys') accu
    | y <= x    = revmergeRev xs' ys (x : accu)
    | otherwise = revmergeRev xs ys' (y : accu)

  push xs k stack | even k = xs : stack
  push xs k stack
    | testBit k 1 =
      let ys : zs : stack' = stack in
      let !xys = revmerge ys xs [] in
      let !xyzs = revmergeRev xys zs [] in
      let !k' = shift k (- 2) in push xyzs k' stack'
    | otherwise =
      let ys : stack' = stack in
      let !xys = revmerge ys xs [] in xys : stack'

  pop xs k [] = xs
  pop xs k stack | odd k =
    let ys : stack' = stack in
    let !xys = revmerge ys xs [] in
    let !k' = shift k (- 1) in popRev xys k' stack'
  pop xs k stack
    | testBit k 1 =
      let !xs' = reverse xs in
      let !k' = shift k (- 1) in popRev xs' k' stack
    | otherwise = let !k' = shift k (- 2) in pop xs k' stack
  popRev xs k [] = reverse xs
  popRev xs k stack | odd k =
    let ys : stack' = stack in
    let !xys = revmergeRev xs ys [] in
    let !k' = shift k (- 1) in pop xys k' stack'
  popRev xs k stack
    | testBit k 1 =
      let !xs' = reverse xs in
      let !k' = shift k (- 1) in pop xs' k' stack
    | otherwise = let !k' = shift k (- 2) in popRev xs k' stack

  sortRec k stack (x : y : z : s)
    | x <= y,       y <= z       = ascending (\s -> x : y : s) z s
    | not (x <= y), not (y <= z) = descending [y, x] z s
    | x <= y      , not (y <= z) =
      let !k' = k + 1 in
      let !xyz = if x <= z then [x, z, y] else [z, x, y] in
      let !stack' = push xyz k stack in sortRec k' stack' s
    | not (x <= y), y <= z =
      let !k' = k + 1 in
      let !xyz = if x <= z then [y, x, z] else [y, z, x] in
      let !stack' = push xyz k stack in sortRec k' stack' s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs k stack
      ascending accu x (y : s) | x <= y =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) k stack
      descending accu x (y : s) | not (x <= y) = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if x <= y then s else [y, x] in pop xy k stack
  sortRec k stack s = pop s k stack
