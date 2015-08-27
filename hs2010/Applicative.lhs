% -*- LaTeX -*-
% $Id: Applicative.lhs 3173 2015-08-27 11:11:37Z wlux $
%
% Copyright (c) 2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{hs2010/Applicative.lhs}
Current systems already come equipped with an implementation of these
classes and we must make use of that to be prepared for the Haskell
2014 \href{https://wiki.haskell.org/Functor-Applicative-Monad_Proposal}%
{Functor-Applicative-Monad proposal}.
\begin{verbatim}

> module Applicative(module Control.Applicative, sequenceA) where
> import Control.Applicative
> import Data.Traversable

\end{verbatim}
