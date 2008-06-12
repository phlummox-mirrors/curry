% -*- LaTeX -*-
% $Id: TypeTrans.lhs 2719 2008-06-12 15:15:07Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeTrans.lhs}
\section{Type Transformations}
This module implements transformations between the internal and
external type representations.
\begin{verbatim}

> module TypeTrans(toType, toTypes, fromType,
>                  expandMonoType, expandMonoTypes, expandPolyType,
>                  ppType, ppTypeScheme) where
> import Base
> import Curry
> import CurryPP
> import List
> import Map
> import PredefIdent
> import PredefTypes
> import Pretty
> import TopEnv
> import Types
> import TypeInfo
> import TypeSubst

\end{verbatim}
The functions \texttt{toType} and \texttt{toTypes} convert Curry type
expressions into types. Type variables are assigned ascending indices
in the order of their occurrence in the types. It is possible to pass
a list of additional type variables to both functions, which are
assigned indices before those variables occurring in the type. This
allows preserving the order of type variables in the left hand side of
a type declaration.

Note the subtle difference between \texttt{toTypes tvs tys} and
\texttt{map (toType tvs) tys}. The former ensures that consistent
indices are assigned to all type variables occurring in the type
expressions \texttt{tys}, whereas the latter assigns type variable
indices independently for each type expression.
\begin{verbatim}

> toType :: [Ident] -> TypeExpr -> Type
> toType tvs ty = toType' (enumTypeVars tvs ty) ty

> toTypes :: [Ident] -> [TypeExpr] -> [Type]
> toTypes tvs tys = map (toType' (enumTypeVars tvs tys)) tys

> enumTypeVars :: Expr a => [Ident] -> a -> FM Ident Int
> enumTypeVars tvs ty = fromListFM (zip (tvs ++ tvs') [0..])
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> toType' :: FM Ident Int -> TypeExpr -> Type
> toType' tvs (ConstructorType tc tys) =
>   TypeConstructor tc (map (toType' tvs) tys)
> toType' tvs (VariableType tv) =
>   maybe (internalError ("toType " ++ show tv)) TypeVariable (lookupFM tv tvs)
> toType' tvs (TupleType tys) = tupleType (map (toType' tvs) tys)
> toType' tvs (ListType ty) = listType (toType' tvs ty)
> toType' tvs (ArrowType ty1 ty2) =
>   TypeArrow (toType' tvs ty1) (toType' tvs ty2)

\end{verbatim}
The function \texttt{fromType} converts a type into a Curry type
expression.
\begin{verbatim}

> fromType :: [Ident] -> Type -> TypeExpr
> fromType tvs (TypeConstructor tc tys)
>   | tc' == listId && length tys == 1 = ListType (head tys')
>   | isTupleId tc' = TupleType tys'
>   | otherwise = ConstructorType tc tys'
>   where tc' = unqualify tc
>         tys' = map (fromType tvs) tys
> fromType tvs (TypeVariable tv) =
>   VariableType (if tv >= 0 then tvs !! tv else mkIdent ('_' : show (-tv)))
> fromType tvs (TypeConstrained tys _) = fromType tvs (head tys)
> fromType tvs (TypeArrow ty1 ty2) =
>   ArrowType (fromType tvs ty1) (fromType tvs ty2)
> fromType _ (TypeSkolem k) = VariableType (mkIdent ("_?" ++ show k))

\end{verbatim}
The functions \texttt{expandMonoType}, \texttt{expandMonoTypes}, and
\texttt{expandPolyType} convert type expressions into types and also
expand all type synonyms and qualify all type constructors during the
conversion. Qualification and expansion are performed at the same
time, since type constructors are recorded in the type constructor
environment using the names visible in the source code, but the
expanded types refer to the original names.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs = expandType tcEnv . toType tvs

> expandMonoTypes :: TCEnv -> [Ident] -> [TypeExpr] -> [Type]
> expandMonoTypes tcEnv tvs = map (expandType tcEnv) . toTypes tvs

> expandPolyType :: TCEnv -> TypeExpr -> TypeScheme
> expandPolyType tcEnv = polyType . normalize 0 . expandMonoType tcEnv []

> expandType :: TCEnv -> Type -> Type
> expandType tcEnv (TypeConstructor tc tys) =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType tc' _ _] -> TypeConstructor tc' tys'
>     [RenamingType tc' _ _] -> TypeConstructor tc' tys'
>     [AliasType _ _ ty] -> expandAliasType tys' ty
>     _ -> internalError ("expandType " ++ show tc)
>   where tys' = map (expandType tcEnv) tys
> expandType _ (TypeVariable tv) = TypeVariable tv
> expandType _ (TypeConstrained tys tv) = TypeConstrained tys tv
> expandType tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (expandType tcEnv ty1) (expandType tcEnv ty2)
> expandType _ (TypeSkolem k) = TypeSkolem k

\end{verbatim}
The following functions implement pretty-printing for types by
converting them into type expressions. In order to improve
readability, module qualifiers are removed as far as possible.
\begin{verbatim}

> ppType :: TCEnv -> Type -> Doc
> ppType tcEnv = ppTypeExpr 0 . fromType nameSupply . unqualifyType tcEnv

> ppTypeScheme :: TCEnv -> TypeScheme -> Doc
> ppTypeScheme tcEnv (ForAll _ ty) = ppType tcEnv ty

> unqualifyType :: TCEnv -> Type -> Type
> unqualifyType tcEnv (TypeConstructor tc tys) =
>   TypeConstructor (unqualifyTC tcEnv tc) (map (unqualifyType tcEnv) tys)
> unqualifyType _ (TypeVariable tv) = TypeVariable tv
> unqualifyType tcEnv (TypeConstrained tys tv) =
>   TypeConstrained (map (unqualifyType tcEnv) tys) tv
> unqualifyType tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (unqualifyType tcEnv ty1) (unqualifyType tcEnv ty2)
> unqualifyType _ (TypeSkolem k) = TypeSkolem k

> unqualifyTC :: TCEnv -> QualIdent -> QualIdent
> unqualifyTC tcEnv tc
>   | isPrimTypeId tc' = qualify tc'
>   | otherwise =
>       case lookupTopEnv tc' tcEnv of
>         [t] | origName t == tc -> qualify tc'
>         _ -> tc
>   where tc' = unqualify tc

\end{verbatim}
