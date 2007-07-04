% -*- LaTeX -*-
% $Id: Trust.lhs 2382 2007-07-04 14:37:05Z wlux $
%
% Copyright (c) 2006-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Trust.lhs}
\section{Collecting Trust Annotations}
The module \texttt{Trust} computes the trust annotation environment.
It is applied to the desugared source code in order to allow providing
trust annotations for anonymous lambda abstractions. Since lambda
abstractions have no name and the desugarer does not change scopes, a
lambda abstraction is trusted if its enclosing function is trusted.
There is no need to check the annotations because this happens already
while checking the definitions of the module.
\begin{verbatim}

> module Trust(trustEnv) where
> import Base
> import Env

\end{verbatim}
The function \texttt{trustEnv} collects the trust attributes from all
trust annotations in the source code. In addition, a default trust
attribute is assigned to all defined functions for which there is no
explicit annotation. By default, local functions inherit the trust
attribute of their enclosing function. The default trust attribute for
global functions is controlled by the \texttt{--trusted} compiler
option. The default trust annotations \verb|{-# TRUST _ #-}| and
\verb|{-# SUSPECT _ #-}| override the inherited attribute for all
declarations without an explicit trust annotation in the same
declaration group. Note that default trust annotations apply to the
right hand sides of pattern declarations, but not to the body of a
declaration group. Thus, in the following, contrived example
\begin{verbatim}
{-# SUSPECT f #-}
f x = let g x = x in h (g z)
  where {-# TRUST _ #-}
        h _ = z
        z = let i y = y in i x
\end{verbatim}
the local functions \texttt{h} and \texttt{i} are trusted, but
\texttt{g} is not.
\begin{verbatim}

> trustEnv :: Trust -> Module -> TrustEnv
> trustEnv tr (Module _ _ _ ds) = trust tr [d | BlockDecl d <- ds] emptyEnv

> class SyntaxTree a where
>   trust :: Trust -> a -> TrustEnv -> TrustEnv

>   trustList :: Trust -> [a] -> TrustEnv -> TrustEnv
>   trustList tr xs env = foldr (trust tr) env xs

> instance SyntaxTree a => SyntaxTree [a] where
>   trust = trustList

> instance SyntaxTree Decl where
>   trust tr (FunctionDecl _ f eqs) env =
>     case lookupEnv f env of
>       Just tr' -> trust tr' eqs env
>       Nothing -> trust tr eqs (bindEnv f tr env)
>   trust tr (PatternDecl _ _ rhs) env = trust tr rhs env
>   trust _ _ env = env

>   trustList tr ds env = foldr (trust tr') env' ds
>     where tr' = head $ [tr | TrustAnnot _ tr [] <- ds] ++ [tr]
>           env' =
>             foldr ($) env [bindEnv f tr | TrustAnnot _ tr fs <- ds, f <- fs]

> instance SyntaxTree Equation where
>   trust tr (Equation _ _ rhs) = trust tr rhs

> instance SyntaxTree Rhs where
>   trust tr (SimpleRhs _ e ds) = trust tr e . trust tr ds

> instance SyntaxTree Expression where
>   trust _ (Literal _) = id
>   trust _ (Variable _) = id
>   trust _ (Constructor _) = id
>   trust tr (Apply e1 e2) = trust tr e1 . trust tr e2
>   trust tr (Let ds e) = trust tr ds . trust tr e
>   trust tr (Case e as) = trust tr e . trust tr as

> instance SyntaxTree Alt where
>   trust tr (Alt _ _ rhs) = trust tr rhs

\end{verbatim}
