module Main where

import Data.Function
import Test.QuickCheck
import qualified Data.List
import qualified MergesortHaskellNTRStack
import qualified MergesortHaskellNTRStack_
import qualified MergesortHaskellTRStack
import qualified MergesortHaskellTRStack_
import qualified MergesortHaskellStdlib

spec_ntrcount_sort3 :: [(Int, Int)] -> Bool
spec_ntrcount_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack.sort3 ((<=) `on` fst) xs

spec_ntrcount_sortN :: [(Int, Int)] -> Bool
spec_ntrcount_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack.sortN ((<=) `on` fst) xs

spec_ntrcount_sort3N :: [(Int, Int)] -> Bool
spec_ntrcount_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack.sort3N ((<=) `on` fst) xs

spec_ntrstack_sort3 :: [(Int, Int)] -> Bool
spec_ntrstack_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack_.sort3 ((<=) `on` fst) xs

spec_ntrstack_sortN :: [(Int, Int)] -> Bool
spec_ntrstack_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack_.sortN ((<=) `on` fst) xs

spec_ntrstack_sort3N :: [(Int, Int)] -> Bool
spec_ntrstack_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack_.sort3N ((<=) `on` fst) xs

spec_trcount_sort3 :: [(Int, Int)] -> Bool
spec_trcount_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack.sort3 ((<=) `on` fst) xs

spec_trcount_sortN :: [(Int, Int)] -> Bool
spec_trcount_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack.sortN ((<=) `on` fst) xs

spec_trcount_sort3N :: [(Int, Int)] -> Bool
spec_trcount_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack.sort3N ((<=) `on` fst) xs

spec_trstack_sort3 :: [(Int, Int)] -> Bool
spec_trstack_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack_.sort3 ((<=) `on` fst) xs

spec_trstack_sortN :: [(Int, Int)] -> Bool
spec_trstack_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack_.sortN ((<=) `on` fst) xs

spec_trstack_sort3N :: [(Int, Int)] -> Bool
spec_trstack_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack_.sort3N ((<=) `on` fst) xs

spec_stdlib_oldSort :: [(Int, Int)] -> Bool
spec_stdlib_oldSort xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellStdlib.oldSort ((<=) `on` fst) xs

spec_stdlib_newSort :: [(Int, Int)] -> Bool
spec_stdlib_newSort xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellStdlib.newSort ((<=) `on` fst) xs

main = do
  quickCheck spec_ntrcount_sort3
  quickCheck spec_ntrcount_sortN
  quickCheck spec_ntrcount_sort3N
  quickCheck spec_ntrstack_sort3
  quickCheck spec_ntrstack_sortN
  quickCheck spec_ntrstack_sort3N
  quickCheck spec_trcount_sort3
  quickCheck spec_trcount_sortN
  quickCheck spec_trcount_sort3N
  quickCheck spec_trstack_sort3
  quickCheck spec_trstack_sortN
  quickCheck spec_trstack_sort3N
  quickCheck spec_stdlib_oldSort
  quickCheck spec_stdlib_newSort
