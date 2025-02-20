-- Stack-based bottom-up tail-recursive mergesorts
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellTRStack where

import Data.List
import Data.Bits

catrev [] ys = ys
catrev (x : xs) ys = catrev xs (x : ys)

sortN :: (a -> a -> Ordering) -> [a] -> [a]
sortN cmp = sortRec [] where
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

  push xs [] = [xs]
  push xs ([] : stack) = xs : stack
  push xs [ys] = let !xys = revmerge ys xs [] in [[], xys]
  push xs (ys : [] : stack) = let !xys = revmerge ys xs [] in [] : xys : stack
  push xs (ys : zs : stack) =
    let !xys = revmerge ys xs [] in
    let !xyzs = revmergeRev xys zs [] in [] : [] : push xyzs stack

  pop xs [] = xs
  pop xs ([] : [] : stack) = pop xs stack
  pop xs ([] : stack) = popRev (reverse xs) stack
  pop xs (ys : stack) = let !xys = revmerge ys xs [] in popRev xys stack
  popRev xs [] = reverse xs
  popRev xs ([] : [] : stack) = popRev xs stack
  popRev xs ([] : stack) = pop (reverse xs) stack
  popRev xs (ys : stack) = let !xys = revmergeRev xs ys [] in pop xys stack

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

  push xs [] = [xs]
  push xs ([] : stack) = xs : stack
  push xs [ys] = let !xys = revmerge ys xs [] in [[], xys]
  push xs (ys : [] : stack) = let !xys = revmerge ys xs [] in [] : xys : stack
  push xs (ys : zs : stack) =
    let !xys = revmerge ys xs [] in
    let !xyzs = revmergeRev xys zs [] in [] : [] : push xyzs stack

  pop xs [] = xs
  pop xs ([] : [] : stack) = pop xs stack
  pop xs ([] : stack) = popRev (reverse xs) stack
  pop xs (ys : stack) = let !xys = revmerge ys xs [] in popRev xys stack
  popRev xs [] = reverse xs
  popRev xs ([] : [] : stack) = popRev xs stack
  popRev xs ([] : stack) = pop (reverse xs) stack
  popRev xs (ys : stack) = let !xys = revmergeRev xs ys [] in pop xys stack

  sortRec stack (x : y : z : s)
    | cmp x y /= GT, cmp y z /= GT = ascending (\s -> x : y : s) z s
    | cmp x y == GT, cmp y z == GT = descending [y, x] z s
    | cmp x y /= GT, cmp y z == GT =
      let !xyz = if cmp x z /= GT then [x, z, y] else [z, x, y] in
      let !stack' = push xyz stack in sortRec stack' s
    | cmp x y == GT, cmp y z /= GT =
      let !xyz = if cmp x z /= GT then [y, x, z] else [y, z, x] in
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
