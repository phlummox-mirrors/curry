% -*- LaTeX -*-
% $Id: TypeInfo.lhs 2472 2007-09-19 14:55:02Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
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
expression is saved.

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type. When only some
constructors of a data type are hidden, those constructors are
replaced by underscores in the interface.
\begin{verbatim}

> module TypeInfo where
> import Base
> import Ident
> import Monad
> import TopEnv
> import Types

> type TCEnv = TopEnv TypeInfo
> data TypeInfo = DataType QualIdent Int [Maybe Ident]
>               | RenamingType QualIdent Int Ident
>               | AliasType QualIdent Int Type
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _) = tc
>   merge (DataType tc n cs) (DataType tc' _ cs')
>     | tc == tc' = Just (DataType tc n (mergeData cs cs'))
>     where mergeData cs cs'
>             | null cs = cs'
>             | null cs' = cs
>             | otherwise = zipWith mplus cs cs'
>   merge (DataType tc n _) (RenamingType tc' _ nc)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (DataType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (RenamingType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (AliasType tc n ty) (AliasType tc' _ _)
>     | tc == tc' = Just (AliasType tc n ty)
>   merge _ _ = Nothing

\end{verbatim}
The initial type constructor environment \texttt{initTCEnv} is
initialized with the types of the predefined unit, list, and tuple
types.
\begin{verbatim}

> initTCEnv :: TCEnv
> initTCEnv = foldr (uncurry predefTC) emptyTCEnv predefTypes
>   where emptyTCEnv = emptyTopEnv (Just (map tupleTC tupleTypes))
>         predefTC (TypeConstructor tc tys) cs =
>           predefTopEnv tc (DataType tc (length tys) (map (Just . fst) cs))
>         tupleTC (TypeConstructor tc tys) =
>           DataType tc (length tys) [Just (unqualify tc)]

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

> constructors :: QualIdent -> TCEnv -> [Maybe Ident]
> constructors tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ cs] -> cs
>     [RenamingType _ _ c] -> [Just c]
>     [AliasType _ _ _] -> []
>     _ -> internalError ("constructors " ++ show tc)

\end{verbatim}
