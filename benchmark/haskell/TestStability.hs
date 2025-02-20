module Main where

import Data.Function
import Test.QuickCheck
import qualified Data.List
import qualified MergesortHaskellNTRCount
import qualified MergesortHaskellNTRStack
import qualified MergesortHaskellTRCount
import qualified MergesortHaskellTRStack

spec_ntrcount_sort3 :: [(Int, Int)] -> Bool
spec_ntrcount_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRCount.sort3 (compare `on` fst) xs

spec_ntrcount_sortN :: [(Int, Int)] -> Bool
spec_ntrcount_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRCount.sortN (compare `on` fst) xs

spec_ntrcount_sort3N :: [(Int, Int)] -> Bool
spec_ntrcount_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRCount.sort3N (compare `on` fst) xs

spec_ntrstack_sort3 :: [(Int, Int)] -> Bool
spec_ntrstack_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack.sort3 (compare `on` fst) xs

spec_ntrstack_sortN :: [(Int, Int)] -> Bool
spec_ntrstack_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack.sortN (compare `on` fst) xs

spec_ntrstack_sort3N :: [(Int, Int)] -> Bool
spec_ntrstack_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellNTRStack.sort3N (compare `on` fst) xs

spec_trcount_sort3 :: [(Int, Int)] -> Bool
spec_trcount_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRCount.sort3 (compare `on` fst) xs

spec_trcount_sortN :: [(Int, Int)] -> Bool
spec_trcount_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRCount.sortN (compare `on` fst) xs

spec_trcount_sort3N :: [(Int, Int)] -> Bool
spec_trcount_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRCount.sort3N (compare `on` fst) xs

spec_trstack_sort3 :: [(Int, Int)] -> Bool
spec_trstack_sort3 xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack.sort3 (compare `on` fst) xs

spec_trstack_sortN :: [(Int, Int)] -> Bool
spec_trstack_sortN xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack.sortN (compare `on` fst) xs

spec_trstack_sort3N :: [(Int, Int)] -> Bool
spec_trstack_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs ==
    MergesortHaskellTRStack.sort3N (compare `on` fst) xs

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
