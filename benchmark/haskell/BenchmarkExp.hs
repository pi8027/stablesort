module Main where

import Control.Monad
import qualified Data.List
import qualified MergesortHaskellNTRStack
import qualified MergesortHaskellNTRStack_
import qualified MergesortHaskellTRStack
import qualified MergesortHaskellTRStack_
import qualified MergesortHaskellStdlib
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
    [("Data.List.sort (old)", \n xs -> sorted (take (n `div` 4) (MergesortHaskellStdlib.oldSort (<=) xs))   `seq` return ()),
     ("Data.List.sort (new)", \n xs -> sorted (take (n `div` 4) (MergesortHaskellStdlib.newSort (<=) xs))   `seq` return ()),
     ("NTRStack.sort3",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3 (<=) xs))   `seq` return ()),
     ("NTRStack.sortN",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sortN (<=) xs))   `seq` return ()),
     ("NTRStack.sort3N",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3N (<=) xs))  `seq` return ()),
     ("NTRStack_.sort3",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack_.sort3 (<=) xs))  `seq` return ()),
     ("NTRStack_.sortN",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack_.sortN (<=) xs))  `seq` return ()),
     ("NTRStack_.sort3N",     \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack_.sort3N (<=) xs)) `seq` return ()),
     ("TRStack.sort3",        \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3 (<=) xs))    `seq` return ()),
     ("TRStack.sortN",        \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sortN (<=) xs))    `seq` return ()),
     ("TRStack.sort3N",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3N (<=) xs))   `seq` return ()),
     ("TRStack_.sort3",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack_.sort3 (<=) xs))   `seq` return ()),
     ("TRStack_.sortN",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack_.sortN (<=) xs))   `seq` return ()),
     ("TRStack_.sort3N",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack_.sort3N (<=) xs))  `seq` return ()),
     ("CBNAcc.sort2",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort2 (<=) xs))         `seq` return ()),
     ("CBNAcc.sort3",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort3 (<=) xs))         `seq` return ()),
     ("CBNAcc.sortN",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sortN (<=) xs))         `seq` return ()),
     ("CBVAcc.sort2",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort2 (<=) xs))         `seq` return ()),
     ("CBVAcc.sort3",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort3 (<=) xs))         `seq` return ()),
     ("CBVAcc.sortN",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sortN (<=) xs))         `seq` return ())]
  benchmark
    "haskell-partial-smooth" (map (\i -> 128 * 2 ^ i) [0..14]) (sort_blocks 50)
    [("Data.List.sort (old)", \n xs -> sorted (take (n `div` 4) (MergesortHaskellStdlib.oldSort (<=) xs))   `seq` return ()),
     ("Data.List.sort (new)", \n xs -> sorted (take (n `div` 4) (MergesortHaskellStdlib.newSort (<=) xs))   `seq` return ()),
     ("NTRStack.sort3",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3 (<=) xs))   `seq` return ()),
     ("NTRStack.sortN",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sortN (<=) xs))   `seq` return ()),
     ("NTRStack.sort3N",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack.sort3N (<=) xs))  `seq` return ()),
     ("NTRStack_.sort3",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack_.sort3 (<=) xs))  `seq` return ()),
     ("NTRStack_.sortN",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack_.sortN (<=) xs))  `seq` return ()),
     ("NTRStack_.sort3N",     \n xs -> sorted (take (n `div` 4) (MergesortHaskellNTRStack_.sort3N (<=) xs)) `seq` return ()),
     ("TRStack.sort3",        \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3 (<=) xs))    `seq` return ()),
     ("TRStack.sortN",        \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sortN (<=) xs))    `seq` return ()),
     ("TRStack.sort3N",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack.sort3N (<=) xs))   `seq` return ()),
     ("TRStack_.sort3",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack_.sort3 (<=) xs))   `seq` return ()),
     ("TRStack_.sortN",       \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack_.sortN (<=) xs))   `seq` return ()),
     ("TRStack_.sort3N",      \n xs -> sorted (take (n `div` 4) (MergesortHaskellTRStack_.sort3N (<=) xs))  `seq` return ()),
     ("CBNAcc.sort2",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort2 (<=) xs))         `seq` return ()),
     ("CBNAcc.sort3",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sort3 (<=) xs))         `seq` return ()),
     ("CBNAcc.sortN",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbnAcc.sortN (<=) xs))         `seq` return ()),
     ("CBVAcc.sort2",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort2 (<=) xs))         `seq` return ()),
     ("CBVAcc.sort3",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sort3 (<=) xs))         `seq` return ()),
     ("CBVAcc.sortN",         \n xs -> sorted (take (n `div` 4) (MergesortCoqCbvAcc.sortN (<=) xs))         `seq` return ())]
  benchmark
    "haskell-total-random" (map (\i -> 128 * 2 ^ i) [0..14]) id
    [("Data.List.sort (old)", \_ xs -> sorted (MergesortHaskellStdlib.oldSort (<=) xs)   `seq` return ()),
     ("Data.List.sort (new)", \_ xs -> sorted (MergesortHaskellStdlib.newSort (<=) xs)   `seq` return ()),
     ("NTRStack.sort3",       \_ xs -> sorted (MergesortHaskellNTRStack.sort3 (<=) xs)   `seq` return ()),
     ("NTRStack.sortN",       \_ xs -> sorted (MergesortHaskellNTRStack.sortN (<=) xs)   `seq` return ()),
     ("NTRStack.sort3N",      \_ xs -> sorted (MergesortHaskellNTRStack.sort3N (<=) xs)  `seq` return ()),
     ("NTRStack_.sort3",      \_ xs -> sorted (MergesortHaskellNTRStack_.sort3 (<=) xs)  `seq` return ()),
     ("NTRStack_.sortN",      \_ xs -> sorted (MergesortHaskellNTRStack_.sortN (<=) xs)  `seq` return ()),
     ("NTRStack_.sort3N",     \_ xs -> sorted (MergesortHaskellNTRStack_.sort3N (<=) xs) `seq` return ()),
     ("TRStack.sort3",        \_ xs -> sorted (MergesortHaskellTRStack.sort3 (<=) xs)    `seq` return ()),
     ("TRStack.sortN",        \_ xs -> sorted (MergesortHaskellTRStack.sortN (<=) xs)    `seq` return ()),
     ("TRStack.sort3N",       \_ xs -> sorted (MergesortHaskellTRStack.sort3N (<=) xs)   `seq` return ()),
     ("TRStack_.sort3",       \_ xs -> sorted (MergesortHaskellTRStack_.sort3 (<=) xs)   `seq` return ()),
     ("TRStack_.sortN",       \_ xs -> sorted (MergesortHaskellTRStack_.sortN (<=) xs)   `seq` return ()),
     ("TRStack_.sort3N",      \_ xs -> sorted (MergesortHaskellTRStack_.sort3N (<=) xs)  `seq` return ()),
     ("CBNAcc.sort2",         \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs)         `seq` return ()),
     ("CBNAcc.sort3",         \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs)         `seq` return ()),
     ("CBNAcc.sortN",         \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs)         `seq` return ()),
     ("CBVAcc.sort2",         \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs)         `seq` return ()),
     ("CBVAcc.sort3",         \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs)         `seq` return ()),
     ("CBVAcc.sortN",         \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs)         `seq` return ())]
  benchmark
    "haskell-total-smooth" (map (\i -> 128 * 2 ^ i) [0..14]) (sort_blocks 50)
    [("Data.List.sort (old)", \_ xs -> sorted (MergesortHaskellStdlib.oldSort (<=) xs)   `seq` return ()),
     ("Data.List.sort (new)", \_ xs -> sorted (MergesortHaskellStdlib.newSort (<=) xs)   `seq` return ()),
     ("NTRStack.sort3",       \_ xs -> sorted (MergesortHaskellNTRStack.sort3 (<=) xs)   `seq` return ()),
     ("NTRStack.sortN",       \_ xs -> sorted (MergesortHaskellNTRStack.sortN (<=) xs)   `seq` return ()),
     ("NTRStack.sort3N",      \_ xs -> sorted (MergesortHaskellNTRStack.sort3N (<=) xs)  `seq` return ()),
     ("NTRStack_.sort3",      \_ xs -> sorted (MergesortHaskellNTRStack_.sort3 (<=) xs)  `seq` return ()),
     ("NTRStack_.sortN",      \_ xs -> sorted (MergesortHaskellNTRStack_.sortN (<=) xs)  `seq` return ()),
     ("NTRStack_.sort3N",     \_ xs -> sorted (MergesortHaskellNTRStack_.sort3N (<=) xs) `seq` return ()),
     ("TRStack.sort3",        \_ xs -> sorted (MergesortHaskellTRStack.sort3 (<=) xs)    `seq` return ()),
     ("TRStack.sortN",        \_ xs -> sorted (MergesortHaskellTRStack.sortN (<=) xs)    `seq` return ()),
     ("TRStack.sort3N",       \_ xs -> sorted (MergesortHaskellTRStack.sort3N (<=) xs)   `seq` return ()),
     ("TRStack_.sort3",       \_ xs -> sorted (MergesortHaskellTRStack_.sort3 (<=) xs)   `seq` return ()),
     ("TRStack_.sortN",       \_ xs -> sorted (MergesortHaskellTRStack_.sortN (<=) xs)   `seq` return ()),
     ("TRStack_.sort3N",      \_ xs -> sorted (MergesortHaskellTRStack_.sort3N (<=) xs)  `seq` return ()),
     ("CBNAcc.sort2",         \_ xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs)         `seq` return ()),
     ("CBNAcc.sort3",         \_ xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs)         `seq` return ()),
     ("CBNAcc.sortN",         \_ xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs)         `seq` return ()),
     ("CBVAcc.sort2",         \_ xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs)         `seq` return ()),
     ("CBVAcc.sort3",         \_ xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs)         `seq` return ()),
     ("CBVAcc.sortN",         \_ xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs)         `seq` return ())]
