% -*- LaTeX -*-
% $Id: TypeInfo.lhs 2687 2008-05-01 13:51:44Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeInfo.lhs}
\section{Type Constructors}
For all defined types, the compiler must maintain kind information. At
present, Curry does not support type classes. Therefore, its type
language is first order and the only information that must be recorded
is the arity of each type. For algebraic data types and renaming
types, the compiler also records all data constructors belonging to
that type, for alias types the expanded right hand side type
expression is saved. The constructor lists are used only for the
purpose of creating module interfaces. It is important that the
constructors are ordered in the same way as in the data type's
definition.

Importing and exporting algebraic data types is complicated by the
fact that the constructors of the type may be (partially) hidden in
the interface. This facilitates the definition of abstract data types.
An abstract data type is always represented as a data type without
constructors in the interface.
\begin{verbatim}

> module TypeInfo where
> import Base
> import Ident
> import TopEnv
> import Types

> type TCEnv = TopEnv TypeInfo
> data TypeInfo = DataType QualIdent Int [Ident]
>               | RenamingType QualIdent Int Ident
>               | AliasType QualIdent Int Type
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _) = tc

\end{verbatim}
The initial type constructor environment \texttt{initTCEnv} is empty.
\begin{verbatim}

> initTCEnv :: TCEnv
> initTCEnv = emptyTopEnv

\end{verbatim}
The function \texttt{constrKind} returns the arity of a type
constructor from the type constructor environment and the function
\texttt{constructors} returns the names of the data and newtype
constructors of a type. Both functions are supposed to be used only
after checking for undefined and ambiguous type identifiers and
therefore should not fail.
\begin{verbatim}

> constrKind :: QualIdent -> TCEnv -> Int
> constrKind tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ n _] -> n
>     [RenamingType _ n _] -> n
>     [AliasType _ n _] -> n
>     _ -> internalError ("constrKind " ++ show tc)

> constructors :: QualIdent -> TCEnv -> [Ident]
> constructors tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ cs] -> cs
>     [RenamingType _ _ c] -> [c]
>     [AliasType _ _ _] -> []
>     _ -> internalError ("constructors " ++ show tc)

\end{verbatim}
