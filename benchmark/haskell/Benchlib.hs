module Benchlib where

import Data.List
import Data.Time.Clock.POSIX (getPOSIXTime)
import Text.Printf
import Control.Monad
import Control.DeepSeq
import System.Random
import System.IO
import qualified System.Mem

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
  String -> [Int] -> ([Int] -> [Int]) -> [(String, Int -> [Int] -> IO ())] -> IO ()
benchmark filename size preproc config = do
  let seeds = unfoldr (Just . random) (mkStdGen 0) :: [Int]
  rs <- zipWithM (\size seed -> do
    let input = preproc (genList (mkStdGen seed) size)
    r <- input `deepseq` mapM (\(name, act) -> do
           time <- withTimerMedian 5 (uncurry act) (size, input)
           return (name, time)) config
    printf "size: %7d" size
    mapM_ (uncurry (printf "; %s: %8.6fs")) r
    putStrLn ""
    return (size, map snd r)) size seeds
  withFile (filename ++ ".time.csv") WriteMode $ \handle -> do
    hPrintf handle "Size"
    mapM_ (\(name, _) -> hPrintf handle ", %s" name) config
    hPrintf handle "\n"
    mapM_ (\(size, times) -> do
              hPrintf handle "%d" size
              mapM_ (hPrintf handle ", %f") times
              hPrintf handle "\n") rs

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
