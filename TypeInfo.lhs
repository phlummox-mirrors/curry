% -*- LaTeX -*-
% $Id: TypeInfo.lhs 3010 2010-10-04 09:54:49Z wlux $
%
% Copyright (c) 1999-2010, Wolfgang Lux
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

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type.
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
>   merge (DataType tc1 tvs1 cs1) (DataType tc2 tvs2 cs2)
>     | tc1 == tc2 && tvs1 == tvs2 && (null cs1 || null cs2 || cs1 == cs2) =
>         Just (DataType tc1 tvs1 (if null cs1 then cs2 else cs1))
>   merge (DataType tc1 tvs1 []) (RenamingType tc2 tvs2 nc)
>     | tc1 == tc2 && tvs1 == tvs2 = Just (RenamingType tc1 tvs1 nc)
>   merge (RenamingType tc1 tvs1 nc) (DataType tc2 tvs2 [])
>     | tc1 == tc2 && tvs1 == tvs2 = Just (RenamingType tc1 tvs1 nc)
>   merge (RenamingType tc1 tvs1 nc1) (RenamingType tc2 tvs2 nc2)
>     | tc1 == tc2 && tvs1 == tvs2 && nc1 == nc2 =
>         Just (RenamingType tc1 tvs1 nc1)
>   merge (AliasType tc1 tvs1 ty1) (AliasType tc2 tvs2 ty2)
>     | tc1 == tc2 && tvs1 == tvs2 && ty1 == ty2 = Just (AliasType tc1 tvs1 ty1)
>   merge _ _ = Nothing

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
