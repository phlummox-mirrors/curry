-- $Id: Random.curry 2107 2007-02-23 19:38:21Z wlux $
--
-- Copyright (c) 2004-2007, Wolfgang Lux
-- See ../LICENSE for the full license.

module Random(StdGen, mkStdGen, next, genRange, split,
              random, randomR, randoms, randomRs, randomIO, randomRIO,
              getStdGen, setStdGen, newStdGen, getStdRandom) where
import Integer

data StdGen

foreign import ccall unsafe "random.h primMkStdGen" mkStdGen :: Int -> StdGen

next :: StdGen -> (Int,StdGen)
next rng = randomR (genRange rng) rng

genRange :: StdGen -> (Int,Int)
genRange _ = (minInt,maxInt)

split :: StdGen -> (StdGen,StdGen)
split rng = (mkStdGen x,mkStdGen y)
  where (x,rng') = next rng
  	(y,_) = next rng'

random :: StdGen -> (Int,StdGen)
random = unsafeRandomR minInt maxInt

randomR :: (Int,Int) -> StdGen -> (Int,StdGen)
randomR (lo,hi) | hi >= lo = unsafeRandomR lo hi

unsafeRandomR :: Int -> Int -> StdGen -> (Int,StdGen)
unsafeRandomR lo hi rng = r `seq` (r,rng)
  where r = primNextRStdGen lo hi rng
	foreign import ccall unsafe "random.h"
  		       primNextRStdGen :: Int -> Int -> StdGen -> Int

randoms :: StdGen -> [Int]
randoms = unsafeRandomRs minInt maxInt

randomRs :: (Int,Int) -> StdGen -> [Int]
randomRs (lo,hi) | hi >= lo = unsafeRandomRs lo hi

unsafeRandomRs :: Int -> Int -> StdGen -> [Int]
unsafeRandomRs lo hi rng = x : unsafeRandomRs lo hi rng'
  where (x,rng') = unsafeRandomR lo hi rng

randomIO :: IO Int
randomIO = getStdRandom random

randomRIO :: (Int,Int) -> IO Int
randomRIO range = getStdRandom (randomR range)

foreign import ccall unsafe "random.h primGetStdGen"
	       getStdGen :: IO StdGen
foreign import ccall unsafe "random.h primSetStdGen"
	       setStdGen :: StdGen -> IO ()

newStdGen :: IO StdGen
newStdGen =
  do
    rng <- getStdGen
    let (rng1,rng2) = split rng
    setStdGen rng1
    return rng2

getStdRandom :: (StdGen -> (a,StdGen)) -> IO a
getStdRandom random =
  do
    rng <- getStdGen
    let (x,rng') = random rng
    setStdGen rng'
    return x
