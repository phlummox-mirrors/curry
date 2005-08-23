% -*- LaTeX -*-
% $Id: Error.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Error.lhs}
\section{Errors}\label{sec:error}
The \texttt{Error} type is used for describing the result of a
computation that can fail. In contrast to the standard \texttt{Maybe}
type, its \texttt{Error} case provides for an error message that
describes the failure.
\begin{verbatim}

> module Error where
> import Monad

> data Error a = Ok a | Error String deriving (Eq,Ord,Show)

> instance Functor Error where
>   fmap f (Ok x) = Ok (f x)
>   fmap f (Error e) = Error e

> instance Monad Error where
>   return x = Ok x
>   fail s = Error s
>   Ok x >>= f = f x
>   Error e >>= _ = Error e

> ok :: Error a -> a
> ok (Ok x) = x
> ok (Error e) = error e

> okM :: Monad m => Error a -> m a
> okM (Ok x) = return x
> okM (Error e) = fail e

> emap :: (String -> String) -> Error a -> Error a
> emap _ (Ok x) = Ok x
> emap f (Error e) = Error (f e)

\end{verbatim}
