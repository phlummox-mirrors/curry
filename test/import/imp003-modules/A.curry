module A(module A,module Prelude) where
import Prelude hiding((+),(-),(*),div,mod)
import qualified Prelude

infixl 7 *, /
infixl 6 +, -

(+) = (+.)
(-) = (-.)
(*) = (*.)
(/) = (/.)
