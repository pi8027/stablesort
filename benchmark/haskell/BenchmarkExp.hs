module Main where

import Control.Monad
import qualified Data.List
import qualified MergesortHaskellNTRCount
import qualified MergesortHaskellNTRStack
import qualified MergesortHaskellTRCount
import qualified MergesortHaskellTRStack
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
    [("Data.List.sort",  \n xs -> sorted (take (n `div` 4) (Data.List.sort xs))                          `seq` return ()),
     ("NTRCount.sort3",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRCount.sort3 compare xs))  `seq` return ()),
     ("NTRCount.sortN",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRCount.sortN compare xs))  `seq` return ()),
     ("NTRCount.sort3N", \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRCount.sort3N compare xs)) `seq` return ()),
     ("NTRStack.sort3",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3 compare xs))  `seq` return ()),
     ("NTRStack.sortN",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sortN compare xs))  `seq` return ()),
     ("NTRStack.sort3N", \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3N compare xs)) `seq` return ()),
     ("TRCount.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRCount.sort3 compare xs))   `seq` return ()),
     ("TRCount.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRCount.sortN compare xs))   `seq` return ()),
     ("TRCount.sort3N",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRCount.sort3N compare xs))  `seq` return ()),
     ("TRStack.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3 compare xs))   `seq` return ()),
     ("TRStack.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sortN compare xs))   `seq` return ()),
     ("TRStack.sort3N",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3N compare xs))  `seq` return ()),
     ("CBNAcc.sort2",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort2 (<=) xs))           `seq` return ()),
     ("CBNAcc.sort3",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort3 (<=) xs))           `seq` return ()),
     ("CBNAcc.sortN",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sortN (<=) xs))           `seq` return ()),
     ("CBVAcc.sort2",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort2 (<=) xs))           `seq` return ()),
     ("CBVAcc.sort3",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort3 (<=) xs))           `seq` return ()),
     ("CBVAcc.sortN",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sortN (<=) xs))           `seq` return ())]
  benchmark
    "haskell-partial-smooth" (map (\i -> 128 * 2 ^ i) [0..14]) (sort_blocks 50)
    [("Data.List.sort",  \n xs -> sorted (take (n `div` 4) (Data.List.sort xs))                          `seq` return ()),
     ("NTRCount.sort3",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRCount.sort3 compare xs))  `seq` return ()),
     ("NTRCount.sortN",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRCount.sortN compare xs))  `seq` return ()),
     ("NTRCount.sort3N", \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRCount.sort3N compare xs)) `seq` return ()),
     ("NTRStack.sort3",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3 compare xs))  `seq` return ()),
     ("NTRStack.sortN",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sortN compare xs))  `seq` return ()),
     ("NTRStack.sort3N", \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3N compare xs)) `seq` return ()),
     ("TRCount.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRCount.sort3 compare xs))   `seq` return ()),
     ("TRCount.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRCount.sortN compare xs))   `seq` return ()),
     ("TRCount.sort3N",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRCount.sort3N compare xs))  `seq` return ()),
     ("TRStack.sort3",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3 compare xs))   `seq` return ()),
     ("TRStack.sortN",   \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sortN compare xs))   `seq` return ()),
     ("TRStack.sort3N",  \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3N compare xs))  `seq` return ()),
     ("CBNAcc.sort2",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort2 (<=) xs))           `seq` return ()),
     ("CBNAcc.sort3",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort3 (<=) xs))           `seq` return ()),
     ("CBNAcc.sortN",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sortN (<=) xs))           `seq` return ()),
     ("CBVAcc.sort2",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort2 (<=) xs))           `seq` return ()),
     ("CBVAcc.sort3",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort3 (<=) xs))           `seq` return ()),
     ("CBVAcc.sortN",    \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sortN (<=) xs))           `seq` return ())]
  benchmark
    "haskell-total-random" (map (\i -> 128 * 2 ^ i) [0..14]) id
    [("Data.List.sort",  \_ xs -> sorted (Data.List.sort xs)                          `seq` return ()),
     ("NTRCount.sort3",  \_ xs -> sorted (MergesortHaskellNTRCount.sort3 compare xs)  `seq` return ()),
     ("NTRCount.sortN",  \_ xs -> sorted (MergesortHaskellNTRCount.sortN compare xs)  `seq` return ()),
     ("NTRCount.sort3N", \_ xs -> sorted (MergesortHaskellNTRCount.sort3N compare xs) `seq` return ()),
     ("NTRStack.sort3",  \_ xs -> sorted (MergesortHaskellNTRStack.sort3 compare xs)  `seq` return ()),
     ("NTRStack.sortN",  \_ xs -> sorted (MergesortHaskellNTRStack.sortN compare xs)  `seq` return ()),
     ("NTRStack.sort3N", \_ xs -> sorted (MergesortHaskellNTRStack.sort3N compare xs) `seq` return ()),
     ("TRCount.sort3",   \_ xs -> sorted (MergesortHaskellTRCount.sort3 compare xs)   `seq` return ()),
     ("TRCount.sortN",   \_ xs -> sorted (MergesortHaskellTRCount.sortN compare xs)   `seq` return ()),
     ("TRCount.sort3N",  \_ xs -> sorted (MergesortHaskellTRCount.sort3N compare xs)  `seq` return ()),
     ("TRStack.sort3",   \_ xs -> sorted (MergesortHaskellTRStack.sort3 compare xs)   `seq` return ()),
     ("TRStack.sortN",   \_ xs -> sorted (MergesortHaskellTRStack.sortN compare xs)   `seq` return ()),
     ("TRStack.sort3N",  \_ xs -> sorted (MergesortHaskellTRStack.sort3N compare xs)  `seq` return ()),
     ("CBNAcc.sort2",    \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs)           `seq` return ()),
     ("CBNAcc.sort3",    \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs)           `seq` return ()),
     ("CBNAcc.sortN",    \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs)           `seq` return ()),
     ("CBVAcc.sort2",    \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs)           `seq` return ()),
     ("CBVAcc.sort3",    \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs)           `seq` return ()),
     ("CBVAcc.sortN",    \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs)           `seq` return ())]
  benchmark
    "haskell-total-smooth" (map (\i -> 128 * 2 ^ i) [0..14]) (sort_blocks 50)
    [("Data.List.sort",  \_ xs -> sorted (Data.List.sort xs)                          `seq` return ()),
     ("NTRCount.sort3",  \_ xs -> sorted (MergesortHaskellNTRCount.sort3 compare xs)  `seq` return ()),
     ("NTRCount.sortN",  \_ xs -> sorted (MergesortHaskellNTRCount.sortN compare xs)  `seq` return ()),
     ("NTRCount.sort3N", \_ xs -> sorted (MergesortHaskellNTRCount.sort3N compare xs) `seq` return ()),
     ("NTRStack.sort3",  \_ xs -> sorted (MergesortHaskellNTRStack.sort3 compare xs)  `seq` return ()),
     ("NTRStack.sortN",  \_ xs -> sorted (MergesortHaskellNTRStack.sortN compare xs)  `seq` return ()),
     ("NTRStack.sort3N", \_ xs -> sorted (MergesortHaskellNTRStack.sort3N compare xs) `seq` return ()),
     ("TRCount.sort3",   \_ xs -> sorted (MergesortHaskellTRCount.sort3 compare xs)   `seq` return ()),
     ("TRCount.sortN",   \_ xs -> sorted (MergesortHaskellTRCount.sortN compare xs)   `seq` return ()),
     ("TRCount.sort3N",  \_ xs -> sorted (MergesortHaskellTRCount.sort3N compare xs)  `seq` return ()),
     ("TRStack.sort3",   \_ xs -> sorted (MergesortHaskellTRStack.sort3 compare xs)   `seq` return ()),
     ("TRStack.sortN",   \_ xs -> sorted (MergesortHaskellTRStack.sortN compare xs)   `seq` return ()),
     ("TRStack.sort3N",  \_ xs -> sorted (MergesortHaskellTRStack.sort3N compare xs)  `seq` return ()),
     ("CBNAcc.sort2",    \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs)           `seq` return ()),
     ("CBNAcc.sort3",    \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs)           `seq` return ()),
     ("CBNAcc.sortN",    \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs)           `seq` return ()),
     ("CBVAcc.sort2",    \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs)           `seq` return ()),
     ("CBVAcc.sort3",    \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs)           `seq` return ()),
     ("CBVAcc.sortN",    \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs)           `seq` return ())]
