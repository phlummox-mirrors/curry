% -*- LaTeX -*-
% $Id: ValueInfo.lhs 2721 2008-06-13 16:17:39Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ValueInfo.lhs}
\section{Function and Constructor Types}
In order to test type correctness of a module, the compiler needs to
determine the type of every data constructor, function, and variable
in the module. For the purpose of type checking, there is no need to
distinguish variables and functions. For all entities, their original
names and their types are saved. In addition, the compiler also saves
the (optional) list of field labels for data and newtype constructors
and the arity of functions. The length of the list of field labels of
a data constructor is always equal to the constructor's arity. If a
data or newtype constructor was declared without field labels, an
anonymous identifier is used in place of each of the labels.

Even though value declarations may be nested, the compiler uses a flat
environment for saving type information. This is possible because all
identifiers are renamed by the compiler before it starts computing type
information.
\begin{verbatim}

> module ValueInfo where
> import Base
> import Ident
> import TopEnv
> import Types

> type ValueEnv = TopEnv ValueInfo
> data ValueInfo = DataConstructor QualIdent [Ident] TypeScheme
>                | NewtypeConstructor QualIdent Ident TypeScheme
>                | Value QualIdent Int TypeScheme
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor c _ _) = c
>   origName (NewtypeConstructor c _ _) = c
>   origName (Value x _ _) = x
>   merge (DataConstructor c1 ls1 ty1) (DataConstructor c2 ls2 ty2)
>     | c1 == c2 && ty1 == ty2 =
>         do
>           ls' <- sequence (zipWith mergeLabel ls1 ls2)
>           Just (DataConstructor c1 ls' ty1)
>   merge (NewtypeConstructor c1 l1 ty1) (NewtypeConstructor c2 l2 ty2)
>     | c1 == c2 && ty1 == ty2 =
>         do
>           l' <- mergeLabel l1 l2
>           Just (NewtypeConstructor c1 l' ty1)
>   merge (Value x1 n1 ty1) (Value x2 n2 ty2)
>     | x1 == x2 && n1 == n2 && ty1 == ty2 = Just (Value x1 n1 ty1)
>   merge _ _ = Nothing

> mergeLabel :: Ident -> Ident -> Maybe Ident
> mergeLabel l1 l2
>   | l1 == anonId = Just l2
>   | l2 == anonId = Just l1
>   | l1 == l2 = Just l1
>   | otherwise = Nothing

\end{verbatim}
The initial value type environment \texttt{initDCEnv} is empty.
\begin{verbatim}

> initDCEnv :: ValueEnv
> initDCEnv = emptyTopEnv

\end{verbatim}
The functions \texttt{bindFun} and \texttt{rebindFun} respectively add
and change the type of a function in the value type environment.
\begin{verbatim}

> bindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
> bindFun m f n ty = bindTopEnv m f (Value (qualifyWith m f) n ty)

> rebindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
> rebindFun m f n ty = rebindTopEnv m f (Value (qualifyWith m f) n ty)

\end{verbatim}
The functions \texttt{conType}, \texttt{varType}, and \texttt{funType}
return the type of constructors, pattern variables, and variables in
expressions, respectively, from the type environment. They are
supposed to be used only after checking for duplicate and ambiguous
identifiers and therefore should not fail.

The function \texttt{conType} also returns the list of field labels
associated with the constructor.

The function \texttt{varType} can handle ambiguous identifiers and
returns the first available type. This makes it possible to use
\texttt{varType} in order to determine the type of a locally defined
function even when the function's name is ambiguous.
\begin{verbatim}

> conType :: QualIdent -> ValueEnv -> ([Ident],TypeScheme)
> conType c tyEnv =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ ls ty] -> (ls,ty)
>     [NewtypeConstructor _ l ty] -> ([l],ty)
>     _ -> internalError ("conType " ++ show c)

> varType :: Ident -> ValueEnv -> TypeScheme
> varType v tyEnv =
>   case lookupTopEnv v tyEnv of
>     Value _ _ ty : _ -> ty
>     _ -> internalError ("varType " ++ show v)

> funType :: QualIdent -> ValueEnv -> TypeScheme
> funType f tyEnv =
>   case qualLookupTopEnv f tyEnv of
>     [Value _ _ ty] -> ty
>     _ -> internalError ("funType " ++ show f)

\end{verbatim}
The function \texttt{arity} returns the arity of a constructor or
function and the function \texttt{changeArity} changes the arity of a
(local) function.
\begin{verbatim}

> arity :: QualIdent -> ValueEnv -> Int
> arity x tyEnv =
>   case qualLookupTopEnv x tyEnv of
>     [DataConstructor _ ls _] -> length ls
>     [NewtypeConstructor _ _ _] -> 1
>     [Value _ n _] -> n
>     _ -> internalError ("arity " ++ show x)

> changeArity :: ModuleIdent -> Ident -> Int -> ValueEnv -> ValueEnv
> changeArity m f n tyEnv =
>   case lookupTopEnv f tyEnv of
>     Value _ _ ty : _ -> rebindFun m f n ty tyEnv
>     _ -> internalError ("changeArity " ++ show f)

\end{verbatim}
The function \texttt{isNewtypeConstr} uses the value type environment
in order to distinguish data and newtype constructors.
\begin{verbatim}

> isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
> isNewtypeConstr tyEnv c =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ _ _] -> False
>     [NewtypeConstructor _ _ _] -> True
>     _ -> internalError ("isNewtypeConstr: " ++ show c)

\end{verbatim}
