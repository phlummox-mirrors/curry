% -*- LaTeX -*-
% $Id: ValueInfo.lhs 2498 2007-10-14 13:16:00Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ValueInfo.lhs}
\section{Function and Constructor Types}
In order to test type correctness of a module, the compiler needs to
determine the type of every data constructor, function, and variable
in the module. For the purpose of type checking, there is no need to
distinguish variables and functions. For all entities, their original
names and their types are saved. In addition, the compiler also saves
the arity of functions and data constructors and the optional field
labels of data and newtype constructors. For constructors, the arity
could be computed from the constructor's type. However, this is not
possible in general for functions. Note that the arity of a newtype
constructor is always one, so there is no need to save it explicitly.

Each data and newtype constructor is associated with a list of field
labels for the constructor's arguments. The length of this list is
always equal to the constructor's arity, i.e., there is exactly one
label associated with each newtype constructor. If a constructor was
declared without labels, an anonymous identifier is used in place of
each label. The same holds for labels that are hidden on import or
export.

Even though value declarations may be nested, the compiler uses a flat
environment for saving type information. This is possible because all
identifiers are renamed by the compiler before it starts computing type
information.
\begin{verbatim}

> module ValueInfo where
> import Base
> import Ident
> import PredefTypes
> import TopEnv
> import Types

> type ValueEnv = TopEnv ValueInfo
> data ValueInfo = DataConstructor QualIdent Int [Ident] TypeScheme
>                | NewtypeConstructor QualIdent Ident TypeScheme
>                | Value QualIdent Int TypeScheme
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor c _ _ _) = c
>   origName (NewtypeConstructor c _ _) = c
>   origName (Value x _ _) = x

\end{verbatim}
The initial value type environment \texttt{initDCEnv} is initialized
with the types of the predefined unit, list, and tuple data
constructors.
\begin{verbatim}

> initDCEnv :: ValueEnv
> initDCEnv = foldr (uncurry predefDC) emptyDCEnv (concatMap snd predefTypes)
>   where emptyDCEnv = emptyTopEnv (Just (map tupleDC tupleTypes))
>         predefDC c ty =
>           predefTopEnv c'
>             (DataConstructor c' n (replicate n anonId) (polyType ty))
>           where c' = qualify c
>                 n = arrowArity ty
>         tupleDC ty@(TypeConstructor tc tys) =
>           DataConstructor tc n (replicate n anonId)
>                           (ForAll n (foldr TypeArrow ty tys))
>           where n = length tys

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
function even though the function's name may be ambiguous.
\begin{verbatim}

> conType :: QualIdent -> ValueEnv -> ([Ident],TypeScheme)
> conType c tyEnv =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ _ ls ty] -> (ls,ty)
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
>     [DataConstructor _ n _ _] -> n
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
>     [DataConstructor _ _ _ _] -> False
>     [NewtypeConstructor _ _ _] -> True
>     _ -> internalError ("isNewtypeConstr: " ++ show c)

\end{verbatim}
