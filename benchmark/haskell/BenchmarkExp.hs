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
    "haskell-partial-random" (map (\i -> 128 * 2 ^ i) [0..14]) id
    [("Data.List.sort", \n xs -> sorted (take (n `div` 4) (Data.List.sort xs))                `seq` return ()),
     ("CBNAcc.sort2",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBNAcc.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sortN (<=) xs)) `seq` return ()),
     ("CBVAcc.sort2",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBVAcc.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sortN (<=) xs)) `seq` return ())]
  benchmark
    "haskell-partial-smooth" (map (\i -> 128 * 2 ^ i) [0..14]) (sort_blocks 50)
    [("Data.List.sort", \n xs -> sorted (take (n `div` 4) (Data.List.sort xs))                `seq` return ()),
     ("CBNAcc.sort2",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBNAcc.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sortN (<=) xs)) `seq` return ()),
     ("CBVAcc.sort2",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBVAcc.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sortN (<=) xs)) `seq` return ())]
  benchmark
    "haskell-total-random" (map (\i -> 128 * 2 ^ i) [0..14]) id
    [("Data.List.sort", \_ xs -> sorted (Data.List.sort xs)                `seq` return ()),
     ("CBNAcc.sort2",   \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs) `seq` return ()),
     ("CBNAcc.sort3",   \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs) `seq` return ()),
     ("CBNAcc.sortN",   \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs) `seq` return ()),
     ("CBVAcc.sort2",   \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs) `seq` return ()),
     ("CBVAcc.sort3",   \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs) `seq` return ()),
     ("CBVAcc.sortN",   \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs) `seq` return ())]
  benchmark
    "haskell-total-smooth" (map (\i -> 128 * 2 ^ i) [0..14]) (sort_blocks 50)
    [("Data.List.sort", \_ xs -> sorted (Data.List.sort xs)                `seq` return ()),
     ("CBNAcc.sort2",   \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs) `seq` return ()),
     ("CBNAcc.sort3",   \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs) `seq` return ()),
     ("CBNAcc.sortN",   \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs) `seq` return ()),
     ("CBVAcc.sort2",   \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs) `seq` return ()),
     ("CBVAcc.sort3",   \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs) `seq` return ()),
     ("CBVAcc.sortN",   \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs) `seq` return ())]
