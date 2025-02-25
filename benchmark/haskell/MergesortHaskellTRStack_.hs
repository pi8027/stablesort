-- Stack-based bottom-up tail-recursive mergesorts without the counter
{-# LANGUAGE BangPatterns #-}
module MergesortHaskellTRStack_ where

import Data.List
import Data.Bits

catrev [] ys = ys
catrev (x : xs) ys = catrev xs (x : ys)

sort3 :: (a -> a -> Bool) -> [a] -> [a]
sort3 (<=) = sortRec [] where
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

  sortRec stack (x : y : z : s) =
    let xyz = if x <= y then
                if y <= z then [x, y, z]
                else if x <= z then [x, z, y] else [z, x, y]
              else
                if x <= z then [y, x, z]
                else if y <= z then [y, z, x] else [z, y, x]
    in
    let !stack' = push xyz stack in sortRec stack' s
  sortRec stack s@[x, y] =
    let !xy = if x <= y then s else [y, x] in pop xy stack
  sortRec stack s = pop s stack

sortN :: (a -> a -> Bool) -> [a] -> [a]
sortN (<=) = sortRec [] where
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
    if x <= y then ascending (x :) y s else descending [x] y s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | x <= y =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !xs = accu [x] in
        let !stack' = push xs stack in sortRec stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | not (x <= y) = descending (x : accu) y s
      descending accu x s =
        let !stack' = push (x : accu) stack in sortRec stack' s
  sortRec stack s = pop s stack

sort3N :: (a -> a -> Bool) -> [a] -> [a]
sort3N (<=) = sortRec [] where
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
    | x <= y,       y <= z       = ascending (\s -> x : y : s) z s
    | not (x <= y), not (y <= z) = descending [y, x] z s
    | x <= y,       not (y <= z) =
      let !xyz = if x <= z then [x, z, y] else [z, x, y] in
      let !stack' = push xyz stack in sortRec stack' s
    | not (x <= y), y <= z =
      let !xyz = if x <= z then [y, x, z] else [y, z, x] in
      let !stack' = push xyz stack in sortRec stack' s
    where
      ascending accu x [] = let !xs = accu [x] in pop xs stack
      ascending accu x (y : s) | x <= y =
        ascending (\ys -> accu (x : ys)) y s
      ascending accu x s =
        let !xs = accu [x] in
        let !stack' = push xs stack in sortRec stack' s

      descending accu x [] = pop (x : accu) stack
      descending accu x (y : s) | not (x <= y) = descending (x : accu) y s
      descending accu x s =
        let !stack' = push (x : accu) stack in sortRec stack' s
  sortRec stack s@[x, y] =
    let !xy = if x <= y then s else [y, x] in pop xy stack
  sortRec stack s = pop s stack
