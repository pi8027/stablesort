module Main where

import Control.Monad
import qualified Data.List
import qualified MergesortCoqCbn
import qualified MergesortCoqCbnAcc
import qualified MergesortCoqCbv
import qualified MergesortCoqCbvAcc
import qualified GHC.Stats

import Benchlib

main :: IO ()
main = do
  statsEnabled <- GHC.Stats.getRTSStatsEnabled
  unless statsEnabled (error "+RTS -T required.")
  benchmark
    "haskell1" (map (25000 *) [1..40]) id
    [("Data.List.sort", \_ xs -> sorted (take 1000 (Data.List.sort xs))                `seq` return ()),
     ("CBN.sort1",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sort1    (<=) xs)) `seq` return ()),
     ("CBN.sort2",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sort2    (<=) xs)) `seq` return ()),
     ("CBN.sort3",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sort3    (<=) xs)) `seq` return ()),
     ("CBN.sortN",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sortN    (<=) xs)) `seq` return ()),
     ("CBNAcc.sort1",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort2",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort3",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBNAcc.sortN",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sortN (<=) xs)) `seq` return ()),
     ("CBV.sort1",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sort1    (<=) xs)) `seq` return ()),
     ("CBV.sort2",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sort2    (<=) xs)) `seq` return ()),
     ("CBV.sort3",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sort3    (<=) xs)) `seq` return ()),
     ("CBV.sortN",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sortN    (<=) xs)) `seq` return ()),
     ("CBVAcc.sort1",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort2",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort3",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBVAcc.sortN",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sortN (<=) xs)) `seq` return ())]
  benchmark
    "haskell2" (map (25000 *) [1..40]) (sort_blocks 50)
    [("Data.List.sort", \_ xs -> sorted (take 1000 (Data.List.sort xs))                `seq` return ()),
     ("CBN.sort1",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sort1    (<=) xs)) `seq` return ()),
     ("CBN.sort2",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sort2    (<=) xs)) `seq` return ()),
     ("CBN.sort3",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sort3    (<=) xs)) `seq` return ()),
     ("CBN.sortN",      \_ xs -> sorted (take 1000 (MergesortCoqCbn.sortN    (<=) xs)) `seq` return ()),
     ("CBNAcc.sort1",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort2",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort3",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBNAcc.sortN",   \_ xs -> sorted (take 1000 (MergesortCoqCbnAcc.sortN (<=) xs)) `seq` return ()),
     ("CBV.sort1",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sort1    (<=) xs)) `seq` return ()),
     ("CBV.sort2",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sort2    (<=) xs)) `seq` return ()),
     ("CBV.sort3",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sort3    (<=) xs)) `seq` return ()),
     ("CBV.sortN",      \_ xs -> sorted (take 1000 (MergesortCoqCbv.sortN    (<=) xs)) `seq` return ()),
     ("CBVAcc.sort1",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort2",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort3",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBVAcc.sortN",   \_ xs -> sorted (take 1000 (MergesortCoqCbvAcc.sortN (<=) xs)) `seq` return ())]
  benchmark
    "haskell3" (map (25000 *) [1..40]) id
    [("Data.List.sort", \_ xs -> sorted (Data.List.sort xs)                `seq` return ()),
     ("CBN.sort1",      \_ xs -> sorted (MergesortCoqCbn.sort1    (<=) xs) `seq` return ()),
     ("CBN.sort2",      \_ xs -> sorted (MergesortCoqCbn.sort2    (<=) xs) `seq` return ()),
     ("CBN.sort3",      \_ xs -> sorted (MergesortCoqCbn.sort3    (<=) xs) `seq` return ()),
     ("CBN.sortN",      \_ xs -> sorted (MergesortCoqCbn.sortN    (<=) xs) `seq` return ()),
     ("CBNAcc.sort1",   \_ xs -> sorted (MergesortCoqCbnAcc.sort1 (<=) xs) `seq` return ()),
     ("CBNAcc.sort2",   \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs) `seq` return ()),
     ("CBNAcc.sort3",   \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs) `seq` return ()),
     ("CBNAcc.sortN",   \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs) `seq` return ()),
     ("CBV.sort1",      \_ xs -> sorted (MergesortCoqCbv.sort1    (<=) xs) `seq` return ()),
     ("CBV.sort2",      \_ xs -> sorted (MergesortCoqCbv.sort2    (<=) xs) `seq` return ()),
     ("CBV.sort3",      \_ xs -> sorted (MergesortCoqCbv.sort3    (<=) xs) `seq` return ()),
     ("CBV.sortN",      \_ xs -> sorted (MergesortCoqCbv.sortN    (<=) xs) `seq` return ()),
     ("CBVAcc.sort1",   \_ xs -> sorted (MergesortCoqCbvAcc.sort1 (<=) xs) `seq` return ()),
     ("CBVAcc.sort2",   \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs) `seq` return ()),
     ("CBVAcc.sort3",   \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs) `seq` return ()),
     ("CBVAcc.sortN",   \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs) `seq` return ())]
  benchmark
    "haskell4" (map (25000 *) [1..40]) (sort_blocks 50)
    [("Data.List.sort", \_ xs -> sorted (Data.List.sort xs)                `seq` return ()),
     ("CBN.sort1",      \_ xs -> sorted (MergesortCoqCbn.sort1    (<=) xs) `seq` return ()),
     ("CBN.sort2",      \_ xs -> sorted (MergesortCoqCbn.sort2    (<=) xs) `seq` return ()),
     ("CBN.sort3",      \_ xs -> sorted (MergesortCoqCbn.sort3    (<=) xs) `seq` return ()),
     ("CBN.sortN",      \_ xs -> sorted (MergesortCoqCbn.sortN    (<=) xs) `seq` return ()),
     ("CBNAcc.sort1",   \_ xs -> sorted (MergesortCoqCbnAcc.sort1 (<=) xs) `seq` return ()),
     ("CBNAcc.sort2",   \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs) `seq` return ()),
     ("CBNAcc.sort3",   \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs) `seq` return ()),
     ("CBNAcc.sortN",   \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs) `seq` return ()),
     ("CBV.sort1",      \_ xs -> sorted (MergesortCoqCbv.sort1    (<=) xs) `seq` return ()),
     ("CBV.sort2",      \_ xs -> sorted (MergesortCoqCbv.sort2    (<=) xs) `seq` return ()),
     ("CBV.sort3",      \_ xs -> sorted (MergesortCoqCbv.sort3    (<=) xs) `seq` return ()),
     ("CBV.sortN",      \_ xs -> sorted (MergesortCoqCbv.sortN    (<=) xs) `seq` return ()),
     ("CBVAcc.sort1",   \_ xs -> sorted (MergesortCoqCbvAcc.sort1 (<=) xs) `seq` return ()),
     ("CBVAcc.sort2",   \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs) `seq` return ()),
     ("CBVAcc.sort3",   \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs) `seq` return ()),
     ("CBVAcc.sortN",   \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs) `seq` return ())]
