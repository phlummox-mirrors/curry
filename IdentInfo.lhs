% -*- LaTeX -*-
% $Id: IdentInfo.lhs 2687 2008-05-01 13:51:44Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IdentInfo.lhs}
\section{Type and Value Identifiers}
In order to implement syntax checking, we use two environments that
map type and value identifiers on their kinds.
\begin{verbatim}

> module IdentInfo where
> import Ident
> import List
> import NestEnv
> import TopEnv

\end{verbatim}
At the type level, we distinguish data and renaming types on one side
and synonym types on the other side. Type variables are not recorded.
Type synonyms use a kind of their own so that the compiler can verify
that no type synonyms are used in type expressions in interface files.
The initial type identifier environment \texttt{initTEnv} is empty.
\begin{verbatim}

> type TypeEnv = TopEnv TypeKind
> data TypeKind =
>     Data QualIdent [Ident]
>   | Alias QualIdent
>   deriving (Eq,Show)

> instance Entity TypeKind where
>   origName (Data tc _) = tc
>   origName (Alias tc) = tc
>   merge (Data tc1 cs1) (Data tc2 cs2)
>     | tc1 == tc2 = Just (Data tc1 (cs1 `union` cs2))
>     | otherwise = Nothing
>   merge (Data _ _) (Alias _) = Nothing
>   merge (Alias _) (Data _ _) = Nothing
>   merge (Alias tc1) (Alias tc2)
>     | tc1 == tc2 = Just (Alias tc1)
>     | otherwise = Nothing

> initTEnv :: TypeEnv
> initTEnv = emptyTopEnv

\end{verbatim}
At pattern and expression level, we distinguish constructors on one
side and functions and variables on the other side. Field labels are
represented as variables here, too. Each variable has an associated
list of identifiers, which contains the names of all constructors for
which the variable is also a valid field label. We use the original
names of the constructors because the import paths of the constructors
and labels are not relevant.

Since scopes can be nested in source code, we use a nested environment
for checking source modules and goals, whereas a flat top-level
environment is sufficient for checking import and export declarations.
The initial value identifier environment \texttt{initVEnv} is empty.
\begin{verbatim}

> type FunEnv = TopEnv ValueKind
> type VarEnv = NestEnv ValueKind

> data ValueKind =
>     Constr QualIdent
>   | Var QualIdent [QualIdent]
>   deriving (Eq,Show)

> instance Entity ValueKind where
>   origName (Constr c) = c
>   origName (Var x _) = x
>   merge (Constr c1) (Constr c2)
>     | c1 == c2 = Just (Constr c1)
>     | otherwise = Nothing
>   merge (Constr _) (Var _ _) = Nothing
>   merge (Var _ _) (Constr _) = Nothing
>   merge (Var v1 cs1) (Var v2 cs2)
>     | v1 == v2 = Just (Var v1 (cs1 `union` cs2))
>     | otherwise = Nothing

> initVEnv :: FunEnv
> initVEnv = emptyTopEnv

\end{verbatim}
