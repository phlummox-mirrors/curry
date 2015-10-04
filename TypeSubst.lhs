% -*- LaTeX -*-
% $Id: TypeSubst.lhs 3177 2015-10-04 08:04:49Z wlux $
%
% Copyright (c) 2003-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSubst.lhs}
\section{Type Substitutions}
This module implements substitutions on types.
\begin{verbatim}

> module TypeSubst(module TypeSubst, idSubst,bindSubst,compose) where
> import List
> import Maybe
> import Subst
> import TopEnv
> import Types
> import ValueInfo

> type TypeSubst = Subst Int Type

> class SubstType a where
>   subst :: TypeSubst -> a -> a

> bindVar :: Int -> Type -> TypeSubst -> TypeSubst
> bindVar tv ty = compose (bindSubst tv ty idSubst)

> substVar :: TypeSubst -> Int -> Type
> substVar = substVar' TypeVariable subst

> instance SubstType Type where
>   subst sigma (TypeConstructor tc tys) =
>     TypeConstructor tc (map (subst sigma) tys)
>   subst sigma (TypeVariable tv) = substVar sigma tv
>   subst sigma (TypeConstrained tys tv) =
>     case substVar sigma tv of
>       TypeVariable tv -> TypeConstrained tys tv
>       ty -> ty
>   subst sigma (TypeArrow ty1 ty2) =
>     TypeArrow (subst sigma ty1) (subst sigma ty2)
>   subst sigma (TypeSkolem k) = TypeSkolem k

> instance SubstType TypeScheme where
>   subst sigma (ForAll n ty) =
>     ForAll n (subst (foldr unbindSubst sigma [0..n-1]) ty)

> instance SubstType ValueInfo where
>   subst theta (DataConstructor c ls ty) = DataConstructor c ls ty
>   subst theta (NewtypeConstructor c l ty) = NewtypeConstructor c l ty
>   subst theta (Value v n ty) = Value v n (subst theta ty)

> instance SubstType a => SubstType (TopEnv a) where
>   subst = fmap . subst

\end{verbatim}
The function \texttt{instTypeScheme} instantiates a type scheme by
substituting the given types for the universally quantified type
variables in a type (scheme). After a substitution the compiler must
recompute the type indices for all type variables. Otherwise,
expanding a type synonym like \verb|type Pair' a b = (b,a)| could
break the invariant that the universally quantified type variables are
assigned indices in the order of their occurrence. This is handled by
function \texttt{normalize}. The function has a threshold parameter
that allows preserving the indices of type variables bound on the left
hand side of a type declaration.
\begin{verbatim}

> instTypeScheme :: [Type] -> Type -> Type
> instTypeScheme tys (TypeConstructor tc tys') =
>   TypeConstructor tc (map (instTypeScheme tys) tys')
> instTypeScheme tys (TypeVariable n)
>   | n >= 0 = tys !! n
>   | otherwise = TypeVariable n
> instTypeScheme _ (TypeConstrained tys n) = TypeConstrained tys n
> instTypeScheme tys (TypeArrow ty1 ty2) =
>   TypeArrow (instTypeScheme tys ty1) (instTypeScheme tys ty2)
> instTypeScheme _ (TypeSkolem k) = TypeSkolem k

> normalize :: Int -> Type -> Type
> normalize n ty = instTypeScheme [TypeVariable (occur tv) | tv <- [0..]] ty
>   where tvs' = zip (nub (filter (>= n) (typeVars ty))) [n..]
>         occur tv = fromMaybe tv (lookup tv tvs')

\end{verbatim}
