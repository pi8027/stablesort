module Main where

import Data.Function
import Test.QuickCheck
import qualified Data.List
import qualified MergesortHaskellNTRCount
import qualified MergesortHaskellNTRStack

spec_ntrcount_sortN :: [(Int, Int)] -> Bool
spec_ntrcount_sortN xs =
  Data.List.sortBy (compare `on` fst) xs == 
    MergesortHaskellNTRCount.sortN (compare `on` fst) xs

spec_ntrcount_sort3N :: [(Int, Int)] -> Bool
spec_ntrcount_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs == 
    MergesortHaskellNTRCount.sort3N (compare `on` fst) xs

spec_ntrstack_sortN :: [(Int, Int)] -> Bool
spec_ntrstack_sortN xs =
  Data.List.sortBy (compare `on` fst) xs == 
    MergesortHaskellNTRStack.sortN (compare `on` fst) xs

spec_ntrstack_sort3N :: [(Int, Int)] -> Bool
spec_ntrstack_sort3N xs =
  Data.List.sortBy (compare `on` fst) xs == 
    MergesortHaskellNTRStack.sort3N (compare `on` fst) xs

main = do
  quickCheck spec_ntrcount_sortN
  quickCheck spec_ntrcount_sort3N
  quickCheck spec_ntrstack_sortN
  quickCheck spec_ntrstack_sort3N
