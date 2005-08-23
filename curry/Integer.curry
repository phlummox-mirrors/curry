-- $Id: Integer.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2004-2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Integer(pow, ilog, isqrt, factorial, binomial, abs, max, min,
	       max3, min3, maxlist, minlist, bitTrunc, bitAnd, bitOr,
	       bitNot, bitXor, even, odd) where
import Bits
import Float

--- (pow m n) returns the m raised to the power of n
pow :: Int -> Int -> Int
pow m n
  | n > 0 = let n' = pow m (n `quot` 2) in
  	    if even n then n' * n' else n' * n' * m
  | n == 0 = 1
  | otherwise = 0

--- (ilog n) returns the floor of the logarithm in base 10 of n
ilog :: Int -> Int
ilog n = truncate (log10 (i2f n))

--- (isqrt n) returns the floor of the square root of n.
isqrt :: Int -> Int
isqrt n = truncate (sqrt (i2f n))

--- (factorial n) returns the factorial of n
factorial :: Int -> Int
factorial n = fact 1 n
  where fact f n = if n <= 1 then f else fact (f * n) (n - 1)

--- (binomial n m) returns n*(n-1)*...*(n-m+1)/m*(m-1)*...*1
--- Fails if m <= 0 or n <= m
binomial :: Int -> Int -> Int
binomial n m = foldr1 (*) [n-m+1 .. n] `quot` foldr1 (*) [1 .. m]

--- (abs n) returns the absolute value of n
abs :: Int -> Int
abs n = if n >= 0 then n else -n

--- (max m n) returns the maximum of m and n
max :: Int -> Int -> Int
max m n = if m >= n then m else n

--- (min m n) return the minimum of m and n
min :: Int -> Int -> Int
min m n = if m <= n then m else n

--- (max3 m n o) returns the maximum of m, n, and o
max3 :: Int -> Int -> Int -> Int
max3 m n o = max (max m n) o

--- (min3 m n o) returns the maximum of m, n, and o
min3 :: Int -> Int -> Int -> Int
min3 m n o = min (min m n) o

--- (maxlist l) returns the maximum integer from the list l
maxlist = foldr1 max

--- (minlist l) returns the minimum integer from the list l
minlist = foldr1 min

--- (bitTrunc m n) returns the m least significant bits of n
bitTrunc :: Int -> Int -> Int
bitTrunc n i
  | n <= 0 = 0
  | n >= bitSize i = i
  | otherwise = (1 `shiftL` n - 1) .&. i

--- (bitAnd m n) returns the bitwise and of m and n
bitAnd :: Int -> Int -> Int
bitAnd = (.&.)

--- (bitOr m n) returns the bitwise or of m and n
bitOr :: Int -> Int -> Int
bitOr = (.|.)

--- (bitNot n) returns the bitwise complement of n
bitNot :: Int -> Int
bitNot = complement

--- (bitXor m n) returns the bitwise exclusive or of m and n
bitXor :: Int -> Int -> Int
bitXor = xor

--- (even n) returns whether n is even
even :: Int -> Bool
even n = n `rem` 2 == 0

--- (odd n) returns whether n is odd
odd :: Int -> Bool
odd n = not (even n)
