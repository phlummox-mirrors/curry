-- $Id: AllSolutions.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module AllSolutions(SearchTree(..), getSearchTree, allValuesD, allValuesB,
                    getFirstSolution, getAllSolutions,
                    getAllValues, getAllFailures) where
import Maybe
import Monad
import Unsafe

data SearchTree a = Fail | Val a | Or [SearchTree a]

getSearchTree :: a -> IO (SearchTree a)
getSearchTree x = return (search (\y -> y =:= Unsafe.unshare x))
  where search g =
          case try g of
            [] -> Fail
            [g] -> Val (unpack g)
            gs -> Or (map search gs)

allValuesD :: SearchTree a -> [a]
allValuesD Fail    = []
allValuesD (Val v) = [v]
allValuesD (Or ts) = concatMap allValuesD ts

allValuesB :: SearchTree a -> [a]
allValuesB t = all [t]
  where all ts
          | null ts = []
          | otherwise = [x | Val x <- ts] ++ all [t | Or ts' <- ts, t <- ts']

getFirstSolution :: (a -> Success) -> IO (Maybe a)
getFirstSolution g = liftM listToMaybe (getAllSolutions g)

getAllSolutions :: (a -> Success) -> IO [a]
getAllSolutions g = getAllValues (unpack g)

getAllValues :: a -> IO [a]
getAllValues x = liftM allValuesD (getSearchTree x)

getAllFailures :: a -> (a -> Success) -> IO [a]
getAllFailures x g = getAllValues x >>= filterM (liftM null . getAllValues . g)
