% -*- LaTeX -*-
% $Id: NestEnv.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1999-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{NestEnv.lhs}
\subsection{Nested Environments}
The \texttt{NestEnv} environment type extends top-level environments
(see section~\ref{sec:toplevel-env}) to manage nested scopes. Local
scopes allow only for a single, unambiguous definition.

As a matter of convenience, the module \texttt{TopEnv} is exported by
the module \texttt{NestEnv}.  Thus, only the latter needs to be
imported.
\begin{verbatim}

> module NestEnv(module TopEnv, NestEnv, bindNestEnv,qualBindNestEnv,
>                lookupNestEnv,qualLookupNestEnv,
>                toplevelEnv,globalEnv,nestEnv) where
> import Env
> import TopEnv
> import Ident

> data NestEnv a = GlobalEnv (TopEnv a) | LocalEnv (NestEnv a) (Env Ident a)
>                  deriving Show

> instance Functor NestEnv where
>   fmap f (GlobalEnv env) = GlobalEnv (fmap f env)
>   fmap f (LocalEnv genv env) = LocalEnv (fmap f genv) (fmap f env)

> bindNestEnv :: Ident -> a -> NestEnv a -> NestEnv a
> bindNestEnv x y (GlobalEnv env) = GlobalEnv (bindTopEnv x y env)
> bindNestEnv x y (LocalEnv genv env) =
>   case lookupEnv x env of
>     Just _ -> error "internal error: bindNestEnv"
>     Nothing -> LocalEnv genv (bindEnv x y env)

> qualBindNestEnv :: QualIdent -> a -> NestEnv a -> NestEnv a
> qualBindNestEnv x y (GlobalEnv env) = GlobalEnv (qualBindTopEnv x y env)
> qualBindNestEnv x y (LocalEnv genv env)
>   | isQualified x = error "internal error: qualBindNestEnv"
>   | otherwise =
>       case lookupEnv x' env of
>         Just _ -> error "internal error: qualBindNestEnv"
>         Nothing -> LocalEnv genv (bindEnv x' y env)
>   where x' = unqualify x

> lookupNestEnv :: Ident -> NestEnv a -> [a]
> lookupNestEnv x (GlobalEnv env) = lookupTopEnv x env
> lookupNestEnv x (LocalEnv genv env) =
>   case lookupEnv x env of
>     Just y -> [y]
>     Nothing -> lookupNestEnv x genv

> qualLookupNestEnv :: QualIdent -> NestEnv a -> [a]
> qualLookupNestEnv x env
>   | isQualified x = qualLookupTopEnv x (toplevelEnv env)
>   | otherwise = lookupNestEnv (unqualify x) env

> toplevelEnv :: NestEnv a -> TopEnv a
> toplevelEnv (GlobalEnv env) = env
> toplevelEnv (LocalEnv genv _) = toplevelEnv genv

> globalEnv :: TopEnv a -> NestEnv a
> globalEnv = GlobalEnv

> nestEnv :: NestEnv a -> NestEnv a
> nestEnv env = LocalEnv env emptyEnv

\end{verbatim}
