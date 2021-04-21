import Data.List
import Data.Time.Clock.POSIX (getPOSIXTime)
import Text.Printf
import Control.Monad
import Control.DeepSeq
import System.Random
import qualified System.Mem
import qualified GHC.Stats
import qualified MergesortCoqCbn
import qualified MergesortCoqCbnOpt
import qualified MergesortCoqCbv
import qualified MergesortCoqCbvOpt

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

benchmark :: [Int] -> [(String, [Int] -> IO ())] -> IO ()
benchmark size config = do
  let seeds = unfoldr (Just . random) (mkStdGen 0) :: [Int]
  rs <- zipWithM (\size seed -> do
    let input = genList (mkStdGen seed) size
    r <- input `deepseq` mapM (\(name, act) -> do
           time <- withTimerMedian 5 act input
           return (name, time)) config
    printf "size: %7d" size
    mapM_ (uncurry (printf "; %s: %8.6fs")) r
    putStrLn ""
    return $ map (\(_, time) -> (size, time)) r) size seeds
  printf "%% time consumption\n"
  mapM_ (\res -> do
    printf "\\addplot coordinates {"
    mapM_ (uncurry (printf "(%d, %f) ")) res
    printf "};\n") $ transpose rs

path :: Ord a => a -> [a] -> Bool
path _ [] = True
path x (y : xs) = (x <= y) && path y xs

sorted :: (Ord a) => [a] -> Bool
sorted [] = True
sorted (x : xs) = path x xs

main :: IO ()
main =do
  statsEnabled <- GHC.Stats.getRTSStatsEnabled
  unless statsEnabled (error "+RTS -T required.")
  benchmark
    (map (10000 *) [1..50])
    [("Data.List.sort", \xs -> sorted (take 1000 (Data.List.sort xs)) `seq` return ()),
     ("CBN.sort", \xs -> sorted (take 1000 (MergesortCoqCbn.sort (<=) xs)) `seq` return ()),
     ("CBNOpt.sort", \xs -> sorted (take 1000 (MergesortCoqCbnOpt.sort (<=) xs)) `seq` return ()),
     ("CBV.sort", \xs -> sorted (take 1000 (MergesortCoqCbv.sort (<=) xs)) `seq` return ()),
     ("CBVOpt.sort", \xs -> sorted (take 1000 (MergesortCoqCbvOpt.sort (<=) xs)) `seq` return ())]
  benchmark
    (map (10000 *) [1..50])
    [("Data.List.sort", \xs -> sorted (Data.List.sort xs) `seq` return ()),
     ("CBN.sort", \xs -> sorted (MergesortCoqCbn.sort (<=) xs) `seq` return ()),
     ("CBNOpt.sort", \xs -> sorted (MergesortCoqCbnOpt.sort (<=) xs) `seq` return ()),
     ("CBV.sort", \xs -> sorted (MergesortCoqCbv.sort (<=) xs) `seq` return ()),
     ("CBVOpt.sort", \xs -> sorted (MergesortCoqCbvOpt.sort (<=) xs) `seq` return ())]
