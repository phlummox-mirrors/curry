-- $Id: AllSolutions.curry 1819 2005-11-07 15:56:02Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module AllSolutions(SearchTree(..), getSearchTree, allValuesD, allValuesB,
                    getFirstSolution, getAllSolutions,
                    getAllValues, getAllFailures) where
import Maybe
import Monad

data SearchTree a = Fail | Val a | Or [SearchTree a]

foreign import primitive encapsulate :: a -> IO (a -> Success)

getSearchTree :: a -> IO (SearchTree a)
getSearchTree x = encapsulate x >>= \g -> return (tree g)
  where tree g =
          case try g of
            [] -> Fail
            [g] -> Val (unpack g)
            gs -> Or (map tree gs)

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
