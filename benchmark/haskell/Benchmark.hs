import Data.List
import Data.Time.Clock.POSIX (getPOSIXTime)
import Text.Printf
import Control.Monad
import Control.DeepSeq
import System.Random
import System.IO
import qualified System.Mem
import qualified GHC.Stats
import qualified MergesortCoqCbn
import qualified MergesortCoqCbnAcc
import qualified MergesortCoqCbv
import qualified MergesortCoqCbvAcc

time :: IO a -> IO Double
time act = do
  System.Mem.performMajorGC
  time1 <- realToFrac <$> getPOSIXTime
  _ <- act
  time2 <- realToFrac <$> getPOSIXTime
  return $ time2 - time1

median :: (Ord a, Fractional a) => [a] -> a
median xs =
  let sorted = sort xs in
  if odd (length xs) then
    sorted !! (length xs `div` 2)
  else
    (sorted !! (length xs `div` 2 - 1) + sorted !! (length xs `div` 2)) / 2

withTimerMedian :: Int -> (a -> IO ()) -> a -> IO Double
withTimerMedian n act arg = median <$> mapM (time . act) (replicate n arg)

genList :: StdGen -> Int -> [Int]
genList seed elems =
  take elems (unfoldr (Just . randomR (0, elems - 1)) seed)

benchmark ::
  String -> [Int] -> ([Int] -> [Int]) -> [(String, [Int] -> IO ())] -> IO ()
benchmark filename size preproc config = do
  let seeds = unfoldr (Just . random) (mkStdGen 0) :: [Int]
  rs <- zipWithM (\size seed -> do
    let input = preproc (genList (mkStdGen seed) size)
    r <- input `deepseq` mapM (\(name, act) -> do
           time <- withTimerMedian 5 act input
           return (name, time)) config
    printf "size: %7d" size
    mapM_ (uncurry (printf "; %s: %8.6fs")) r
    putStrLn ""
    return $ map (\(_, time) -> (size, time)) r) size seeds
  withFile (filename ++ ".time.out") WriteMode $ \handle -> do
    hPrintf handle "%% time consumption\n"
    zipWithM_ (\res (name, _) -> do
      hPrintf handle "\\addplot coordinates {"
      mapM_ (uncurry (hPrintf handle "(%d, %f) ")) res
      hPrintf handle "}; %% %s\n" name) (transpose rs) (config)

path :: Ord a => a -> [a] -> Bool
path _ [] = True
path x (y : xs) = (x <= y) && path y xs

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted (x : xs) = path x xs

sort_blocks :: Ord a => Int -> [a] -> [a]
sort_blocks _ [] = []
sort_blocks n xs =
  let (xs1, xs2) = splitAt n xs in sort xs1 ++ sort_blocks n xs2

main :: IO ()
main =do
  statsEnabled <- GHC.Stats.getRTSStatsEnabled
  unless statsEnabled (error "+RTS -T required.")
  benchmark
    "haskell1" (map (25000 *) [1..40]) id
    [("Data.List.sort", \xs -> sorted (take 1000 (Data.List.sort xs))                `seq` return ()),
     ("CBN.sort1",      \xs -> sorted (take 1000 (MergesortCoqCbn.sort1    (<=) xs)) `seq` return ()),
     ("CBN.sort2",      \xs -> sorted (take 1000 (MergesortCoqCbn.sort2    (<=) xs)) `seq` return ()),
     ("CBN.sort3",      \xs -> sorted (take 1000 (MergesortCoqCbn.sort3    (<=) xs)) `seq` return ()),
     ("CBN.sortN",      \xs -> sorted (take 1000 (MergesortCoqCbn.sortN    (<=) xs)) `seq` return ()),
     ("CBNAcc.sort1",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort2",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort3",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBNAcc.sortN",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sortN (<=) xs)) `seq` return ()),
     ("CBV.sort1",      \xs -> sorted (take 1000 (MergesortCoqCbv.sort1    (<=) xs)) `seq` return ()),
     ("CBV.sort2",      \xs -> sorted (take 1000 (MergesortCoqCbv.sort2    (<=) xs)) `seq` return ()),
     ("CBV.sort3",      \xs -> sorted (take 1000 (MergesortCoqCbv.sort3    (<=) xs)) `seq` return ()),
     ("CBV.sortN",      \xs -> sorted (take 1000 (MergesortCoqCbv.sortN    (<=) xs)) `seq` return ()),
     ("CBVAcc.sort1",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort2",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort3",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBVAcc.sortN",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sortN (<=) xs)) `seq` return ())]
  benchmark
    "haskell2" (map (25000 *) [1..40]) (sort_blocks 50)
    [("Data.List.sort", \xs -> sorted (take 1000 (Data.List.sort xs))                `seq` return ()),
     ("CBN.sort1",      \xs -> sorted (take 1000 (MergesortCoqCbn.sort1    (<=) xs)) `seq` return ()),
     ("CBN.sort2",      \xs -> sorted (take 1000 (MergesortCoqCbn.sort2    (<=) xs)) `seq` return ()),
     ("CBN.sort3",      \xs -> sorted (take 1000 (MergesortCoqCbn.sort3    (<=) xs)) `seq` return ()),
     ("CBN.sortN",      \xs -> sorted (take 1000 (MergesortCoqCbn.sortN    (<=) xs)) `seq` return ()),
     ("CBNAcc.sort1",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort2",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBNAcc.sort3",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBNAcc.sortN",   \xs -> sorted (take 1000 (MergesortCoqCbnAcc.sortN (<=) xs)) `seq` return ()),
     ("CBV.sort1",      \xs -> sorted (take 1000 (MergesortCoqCbv.sort1    (<=) xs)) `seq` return ()),
     ("CBV.sort2",      \xs -> sorted (take 1000 (MergesortCoqCbv.sort2    (<=) xs)) `seq` return ()),
     ("CBV.sort3",      \xs -> sorted (take 1000 (MergesortCoqCbv.sort3    (<=) xs)) `seq` return ()),
     ("CBV.sortN",      \xs -> sorted (take 1000 (MergesortCoqCbv.sortN    (<=) xs)) `seq` return ()),
     ("CBVAcc.sort1",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort1 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort2",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort2 (<=) xs)) `seq` return ()),
     ("CBVAcc.sort3",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sort3 (<=) xs)) `seq` return ()),
     ("CBVAcc.sortN",   \xs -> sorted (take 1000 (MergesortCoqCbvAcc.sortN (<=) xs)) `seq` return ())]
  benchmark
    "haskell3" (map (25000 *) [1..40]) id
    [("Data.List.sort", \xs -> sorted (Data.List.sort xs)                `seq` return ()),
     ("CBN.sort1",      \xs -> sorted (MergesortCoqCbn.sort1    (<=) xs) `seq` return ()),
     ("CBN.sort2",      \xs -> sorted (MergesortCoqCbn.sort2    (<=) xs) `seq` return ()),
     ("CBN.sort3",      \xs -> sorted (MergesortCoqCbn.sort3    (<=) xs) `seq` return ()),
     ("CBN.sortN",      \xs -> sorted (MergesortCoqCbn.sortN    (<=) xs) `seq` return ()),
     ("CBNAcc.sort1",   \xs -> sorted (MergesortCoqCbnAcc.sort1 (<=) xs) `seq` return ()),
     ("CBNAcc.sort2",   \xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs) `seq` return ()),
     ("CBNAcc.sort3",   \xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs) `seq` return ()),
     ("CBNAcc.sortN",   \xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs) `seq` return ()),
     ("CBV.sort1",      \xs -> sorted (MergesortCoqCbv.sort1    (<=) xs) `seq` return ()),
     ("CBV.sort2",      \xs -> sorted (MergesortCoqCbv.sort2    (<=) xs) `seq` return ()),
     ("CBV.sort3",      \xs -> sorted (MergesortCoqCbv.sort3    (<=) xs) `seq` return ()),
     ("CBV.sortN",      \xs -> sorted (MergesortCoqCbv.sortN    (<=) xs) `seq` return ()),
     ("CBVAcc.sort1",   \xs -> sorted (MergesortCoqCbvAcc.sort1 (<=) xs) `seq` return ()),
     ("CBVAcc.sort2",   \xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs) `seq` return ()),
     ("CBVAcc.sort3",   \xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs) `seq` return ()),
     ("CBVAcc.sortN",   \xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs) `seq` return ())]
  benchmark
    "haskell4" (map (25000 *) [1..40]) (sort_blocks 50)
    [("Data.List.sort", \xs -> sorted (Data.List.sort xs)                `seq` return ()),
     ("CBN.sort1",      \xs -> sorted (MergesortCoqCbn.sort1    (<=) xs) `seq` return ()),
     ("CBN.sort2",      \xs -> sorted (MergesortCoqCbn.sort2    (<=) xs) `seq` return ()),
     ("CBN.sort3",      \xs -> sorted (MergesortCoqCbn.sort3    (<=) xs) `seq` return ()),
     ("CBN.sortN",      \xs -> sorted (MergesortCoqCbn.sortN    (<=) xs) `seq` return ()),
     ("CBNAcc.sort1",   \xs -> sorted (MergesortCoqCbnAcc.sort1 (<=) xs) `seq` return ()),
     ("CBNAcc.sort2",   \xs -> sorted (MergesortCoqCbnAcc.sort2 (<=) xs) `seq` return ()),
     ("CBNAcc.sort3",   \xs -> sorted (MergesortCoqCbnAcc.sort3 (<=) xs) `seq` return ()),
     ("CBNAcc.sortN",   \xs -> sorted (MergesortCoqCbnAcc.sortN (<=) xs) `seq` return ()),
     ("CBV.sort1",      \xs -> sorted (MergesortCoqCbv.sort1    (<=) xs) `seq` return ()),
     ("CBV.sort2",      \xs -> sorted (MergesortCoqCbv.sort2    (<=) xs) `seq` return ()),
     ("CBV.sort3",      \xs -> sorted (MergesortCoqCbv.sort3    (<=) xs) `seq` return ()),
     ("CBV.sortN",      \xs -> sorted (MergesortCoqCbv.sortN    (<=) xs) `seq` return ()),
     ("CBVAcc.sort1",   \xs -> sorted (MergesortCoqCbvAcc.sort1 (<=) xs) `seq` return ()),
     ("CBVAcc.sort2",   \xs -> sorted (MergesortCoqCbvAcc.sort2 (<=) xs) `seq` return ()),
     ("CBVAcc.sort3",   \xs -> sorted (MergesortCoqCbvAcc.sort3 (<=) xs) `seq` return ()),
     ("CBVAcc.sortN",   \xs -> sorted (MergesortCoqCbvAcc.sortN (<=) xs) `seq` return ())]
