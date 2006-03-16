-- $Id: Success.curry 1872 2006-03-16 10:11:43Z wlux $
--
-- Copyright (c) 2002-2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module Success(module Success, Success, success, (&), (&>)) where
infix  0 ==>, <==

-- Computes the concurrent conjunction of a list of constraints
andC :: [Success] -> Success
andC = foldr (&) success

-- Computes the sequential conjunction of a list of constraints
andS :: [Success] -> Success
andS = foldr (&>) success

-- Is a given predicate satisfied by all elements in a list?
allC :: (a -> Success) -> [a] -> Success
allC p = andC . map p

-- (c ==> x) evaluates x if the constraint c is satisfied
(==>) :: Success -> a -> a
c ==> x | c = x

-- (x <== c) is equivalent to (c ==> x)
(<==) :: a -> Success -> a
x <== c | c = x

-- (choose xs) non-deterministically chooses one element from the list xs
choose (x:xs) = choosep x xs
  where choosep x [] = x
        choosep x (_:_) = x
        choosep _ (x:xs) = choosep x xs

-- (ground e) ensures that e is a ground data term; the argument is
-- evaluated lazily as with Prelude.id
foreign import primitive ground :: a -> a
