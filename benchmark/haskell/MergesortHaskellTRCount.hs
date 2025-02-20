-- Counting-based bottom-up tail-recursive mergesorts
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellTRCount where

import Data.List
import Data.Bits

catrev [] ys = ys
catrev (x : xs) ys = catrev xs (x : ys)

sort3 :: (a -> a -> Ordering) -> [a] -> [a]
sort3 cmp = sortRec (0 :: Int) [] where
  revmerge [] ys accu = catrev ys accu
  revmerge xs [] accu = catrev xs accu
  revmerge xs@(x : xs') ys@(y : ys') accu
    | cmp x y == GT = revmerge xs ys' (y : accu)
    | otherwise     = revmerge xs' ys (x : accu)

  revmergeRev [] ys accu = catrev ys accu
  revmergeRev xs [] accu = catrev xs accu
  revmergeRev xs@(x : xs') ys@(y : ys') accu
    | cmp y x == GT = revmergeRev xs ys' (y : accu)
    | otherwise     = revmergeRev xs' ys (x : accu)

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
    let xyz = if cmp x y /= GT then
                if cmp y z /= GT then [x, y, z]
                else if cmp x z /= GT then [x, z, y] else [z, x, y]
              else
                if cmp x z /= GT then [y, x, z]
                else if cmp y z /= GT then [y, z, x] else [z, y, x]
    in
    let !k' = k + 1 in
    let !stack' = push xyz k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if cmp x y /= GT then s else [y, x] in pop xy k stack
  sortRec k stack s = pop s k stack

sortN :: (a -> a -> Ordering) -> [a] -> [a]
sortN cmp = sortRec (0 :: Int) [] where
  revmerge [] ys accu = catrev ys accu
  revmerge xs [] accu = catrev xs accu
  revmerge xs@(x : xs') ys@(y : ys') accu
    | cmp x y == GT = revmerge xs ys' (y : accu)
    | otherwise     = revmerge xs' ys (x : accu)

  revmergeRev [] ys accu = catrev ys accu
  revmergeRev xs [] accu = catrev xs accu
  revmergeRev xs@(x : xs') ys@(y : ys') accu
    | cmp y x == GT = revmergeRev xs ys' (y : accu)
    | otherwise     = revmergeRev xs' ys (x : accu)

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
    if cmp x y /= GT then ascending (x :) y s else descending [x] y s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs k stack
      ascending accu x (y : s) | cmp x y /= GT =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) k stack
      descending accu x (y : s) | cmp x y == GT = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s = pop s k stack

sort3N :: (a -> a -> Ordering) -> [a] -> [a]
sort3N cmp = sortRec (0 :: Int) [] where
  revmerge [] ys accu = catrev ys accu
  revmerge xs [] accu = catrev xs accu
  revmerge xs@(x : xs') ys@(y : ys') accu
    | cmp x y == GT = revmerge xs ys' (y : accu)
    | otherwise     = revmerge xs' ys (x : accu)

  revmergeRev [] ys accu = catrev ys accu
  revmergeRev xs [] accu = catrev xs accu
  revmergeRev xs@(x : xs') ys@(y : ys') accu
    | cmp y x == GT = revmergeRev xs ys' (y : accu)
    | otherwise     = revmergeRev xs' ys (x : accu)

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
      ascending accu x [] = let !xs = accu [x] in pop xs k stack
      ascending accu x (y : s) | cmp x y /= GT =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !k' = k + 1 in
        let !xs = accu [x] in
        let !stack' = push xs k stack in sortRec k' stack' s

      descending accu x [] = pop (x : accu) k stack
      descending accu x (y : s) | cmp x y == GT = descending (x : accu) y s
      descending accu x s =
        let !k' = k + 1 in
        let !stack' = push (x : accu) k stack in sortRec k' stack' s
  sortRec k stack s@[x, y] =
    let !xy = if cmp x y /= GT then s else [y, x] in pop xy k stack
  sortRec k stack s = pop s k stack
