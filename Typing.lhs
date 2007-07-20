% -*- LaTeX -*-
% $Id: Typing.lhs 2404 2007-07-20 14:39:32Z wlux $
%
% Copyright (c) 2003-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..), NewtypeEnv, newtypeEnv) where
> import Base
> import Combined
> import Env
> import List
> import Maybe
> import Monad
> import TopEnv
> import TypeSubst
> import Utils

\end{verbatim}
During the transformation of Curry source code into the intermediate
language, the compiler has to recompute the types of expressions. This
is simpler than type checking because the types of all variables are
known. Yet, the compiler still must handle functions and constructors
with polymorphic types and instantiate their type schemes using fresh
type variables. Since all types computed by \texttt{typeOf} are
monomorphic, we can use type variables with non-negative offsets for
the instantiation of type schemes here without risk of name conflicts.
Using non-negative offsets also makes it easy to distinguish these
fresh variables from free type variables introduce during type
inference, which must be regarded as constants here.

During desugaring, the compiler will remove newtype constructors and
renaming types effectively become type synonyms. Therefore, given a
definition \texttt{newtype $T\,u_1\dots,u_n$ = $N\,\tau$}, the types
$T\,\tau_1\dots\tau_n$ and $\tau[u_1/\tau_1,\dots,u_n/\tau_n]$ are
considered equal. However, renaming types -- in contrast to type
synonyms -- can be recursive. Therefore, we expand renaming types
lazily during unification with the help of an auxiliary environment
that maps each newtype type constructor $T$ onto the argument type
$\tau$ of its newtype constructor. This environment is initialized
trivially from the value type environment. Note that it always
contains an entry for type \texttt{IO}, which is assumed to be defined
implicitly as
\begin{verbatim}
  newtype IO a = IO (World -> (a,World))
\end{verbatim}
for some abstract type \texttt{World} representing the state of the
external world.
\begin{verbatim}

> type NewtypeEnv = Env QualIdent Type

> newtypeEnv :: ValueEnv -> NewtypeEnv
> newtypeEnv tyEnv = foldr bindNewtype initNewtypeEnv (allEntities tyEnv)
>   where initNewtypeEnv = bindEnv qIOId ioType' emptyEnv
>         ioType' = TypeArrow worldType (tupleType [TypeVariable 0,worldType])
>         worldType = TypeConstructor (qualify (mkIdent "World")) []
>         bindNewtype (DataConstructor _ _ _) = id
>         bindNewtype (NewtypeConstructor _ (ForAll _ ty)) = bindEnv tc ty1
>           where TypeArrow ty1 (TypeConstructor tc _) = ty
>         bindNewtype (Value _ _ _) = id

\end{verbatim}
Using non-negative offsets for fresh type variables gives rise to two
problems when those types are entered back into the type environment,
e.g., while introducing auxiliary variables during desugaring. The
first is that those type variables now appear to be universally
quantified variables, but with indices greater than the number of
quantified type variables.\footnote{To be precise, this can happen
  only for auxiliary variables, which have monomorphic types, whereas
  auxiliary functions will be assigned polymorphic types and these
  type variables will be properly quantified. However, in this case
  the assigned types may be too general.} This results in an internal
error (``Prelude.!!: index too large'') whenever such a type is
instantiated. The second problem is that there may be inadvertent name
captures because \texttt{computeType} always uses indices starting at
0 for the fresh type variables. In order to avoid these problems,
\texttt{computeType} renames all type variables with non-negative
offsets after the final type has been computed, using negative indices
below the one with the smallest value occurring in the type
environment. Computing the minimum index of all type variables in the
type environment seems prohibitively inefficient.  However, recall
that, thanks to laziness, the minimum is computed only when the final
type contains any type variables with non-negative indices. This
happens, for instance, 36 times while compiling the prelude (for 159
evaluated applications of \texttt{typeOf}) and only twice while
compiling the standard \texttt{IO} module (for 21 applications of
\texttt{typeOf}).\footnote{These numbers were obtained for version
  0.9.9.}

A careful reader will note that inadvertent name captures are still
possible if one computes the types of two or more auxiliary variables
before actually entering their types into the environment. Therefore,
make sure that you enter the types of these auxiliary variables
immediately into the type environment, unless you are sure that those
types cannot contain fresh type variables. One such case are the free
variables of a goal.

\ToDo{In the long run, this module should be made obsolete by adding
attributes to the abstract syntax tree -- e.g., along the lines of
Chap.~6 in~\cite{PeytonJonesLester92:Book} -- and returning an
abstract syntax tree attributed with type information together with
the type environment from type inference. This also would allow
getting rid of the identifiers in the representation of integer
literals, which are used in order to implement overloading of
integer constants.}

\ToDo{When computing the type of an expression with a type signature
make use of the annotation instead of recomputing its type. In order
to do this, we must either ensure that the types are properly
qualified and expanded or we need access to the type constructor
environment.}
\begin{verbatim}

> type TyState a = StateT TypeSubst (StateT Int Id) a

> run :: TyState a -> a
> run m = runSt (callSt m idSubst) 0

> class Typeable a where
>   typeOf :: ValueEnv -> a -> Type
>   typeOf' :: NewtypeEnv -> ValueEnv -> a -> Type
>
>   typeOf tyEnv = typeOf' (newtypeEnv tyEnv) tyEnv

> instance Typeable Ident where
>   typeOf' = computeType identType

> instance Typeable ConstrTerm where
>   typeOf' = computeType argType

> instance Typeable Expression where
>   typeOf' = computeType exprType

> instance Typeable Rhs where
>   typeOf' = computeType rhsType

> computeType :: (NewtypeEnv -> ValueEnv -> a -> TyState Type)
>             -> NewtypeEnv -> ValueEnv -> a -> Type
> computeType f nEnv tyEnv x = fixTypeVars tyEnv (run doComputeType)
>   where doComputeType =
>           do
>             ty <- f nEnv tyEnv x
>             theta <- fetchSt
>             return (subst theta ty)

> fixTypeVars :: ValueEnv -> Type -> Type
> fixTypeVars tyEnv ty = subst (foldr2 bindSubst idSubst tvs tvs') ty
>   where tvs = nub (filter (>= 0) (typeVars ty))
>         tvs' = map TypeVariable [n - 1,n - 2 ..]
>         n = minimum (0 : concatMap typeVars tys)
>         tys = [ty | (_,Value _ _ (ForAll _ ty)) <- localBindings tyEnv]

> identType :: NewtypeEnv -> ValueEnv -> Ident -> TyState Type
> identType _ tyEnv x = instUniv (varType x tyEnv)

> litType :: NewtypeEnv -> ValueEnv -> Literal -> TyState Type
> litType _ _ (Char _) = return charType
> litType nEnv tyEnv (Int v _) = identType nEnv tyEnv v
> litType _ _ (Float _) = return floatType
> litType _ _ (String _) = return stringType

> argType :: NewtypeEnv -> ValueEnv -> ConstrTerm -> TyState Type
> argType nEnv tyEnv (LiteralPattern l) = litType nEnv tyEnv l
> argType nEnv tyEnv (NegativePattern _ l) = litType nEnv tyEnv l
> argType nEnv tyEnv (VariablePattern v) = identType nEnv tyEnv v
> argType nEnv tyEnv (ConstructorPattern c ts) =
>   do
>     (tys,ty) <- liftM arrowUnapply (instUniv (conType c tyEnv))
>     tys' <- mapM (argType nEnv tyEnv) ts
>     unifyList nEnv tys tys'
>     return ty
> argType nEnv tyEnv (InfixPattern t1 op t2) =
>   argType nEnv tyEnv (ConstructorPattern op [t1,t2])
> argType nEnv tyEnv (ParenPattern t) = argType nEnv tyEnv t
> argType nEnv tyEnv (TuplePattern ts) =
>   liftM tupleType (mapM (argType nEnv tyEnv) ts)
> argType nEnv tyEnv (ListPattern ts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (elemType ty) ts
>     return (listType ty)
>   where elemType ty t = argType nEnv tyEnv t >>= unify nEnv ty
> argType nEnv tyEnv (AsPattern v _) = argType nEnv tyEnv (VariablePattern v)
> argType nEnv tyEnv (LazyPattern t) = argType nEnv tyEnv t

> exprType :: NewtypeEnv -> ValueEnv -> Expression -> TyState Type
> exprType nEnv tyEnv (Literal l) = litType nEnv tyEnv l
> exprType _ tyEnv (Variable v) = instUniv (funType v tyEnv)
> exprType _ tyEnv (Constructor c) = instUniv (conType c tyEnv)
> exprType nEnv tyEnv (Typed e _) = exprType nEnv tyEnv e
> exprType nEnv tyEnv (Paren e) = exprType nEnv tyEnv e
> exprType nEnv tyEnv (Tuple es) =
>   liftM tupleType (mapM (exprType nEnv tyEnv) es)
> exprType nEnv tyEnv (List es) =
>   do
>     ty <- freshTypeVar
>     mapM_ (elemType ty) es
>     return (listType ty)
>   where elemType ty e = exprType nEnv tyEnv e >>= unify nEnv ty
> exprType nEnv tyEnv (ListCompr e _) = liftM listType (exprType nEnv tyEnv e)
> exprType _ tyEnv (EnumFrom _) = return (listType intType)
> exprType _ tyEnv (EnumFromThen _ _) = return (listType intType)
> exprType _ tyEnv (EnumFromTo _ _) = return (listType intType)
> exprType _ tyEnv (EnumFromThenTo _ _ _) = return (listType intType)
> exprType nEnv tyEnv (UnaryMinus _ e) = exprType nEnv tyEnv e
> exprType nEnv tyEnv (Apply e1 e2) =
>   do
>     (ty1,ty2) <- exprType nEnv tyEnv e1 >>= unifyArrow nEnv
>     exprType nEnv tyEnv e2 >>= unify nEnv ty1
>     return ty2
> exprType nEnv tyEnv (InfixApply e1 op e2) =
>   do
>     (ty1,ty2,ty3) <- exprType nEnv tyEnv (infixOp op) >>= unifyArrow2 nEnv
>     exprType nEnv tyEnv e1 >>= unify nEnv ty1
>     exprType nEnv tyEnv e2 >>= unify nEnv ty2
>     return ty3
> exprType nEnv tyEnv (LeftSection e op) =
>   do
>     (ty1,ty2,ty3) <- exprType nEnv tyEnv (infixOp op) >>= unifyArrow2 nEnv
>     exprType nEnv tyEnv e >>= unify nEnv ty1
>     return (TypeArrow ty2 ty3)
> exprType nEnv tyEnv (RightSection op e) =
>   do
>     (ty1,ty2,ty3) <- exprType nEnv tyEnv (infixOp op) >>= unifyArrow2 nEnv
>     exprType nEnv tyEnv e >>= unify nEnv ty2
>     return (TypeArrow ty1 ty3)
> exprType nEnv tyEnv (Lambda _ ts e) =
>   do
>     tys <- mapM (argType nEnv tyEnv) ts
>     ty <- exprType nEnv tyEnv e
>     return (foldr TypeArrow ty tys)
> exprType nEnv tyEnv (Let _ e) = exprType nEnv tyEnv e
> exprType nEnv tyEnv (Do _ e) = exprType nEnv tyEnv e
> exprType nEnv tyEnv (IfThenElse e1 e2 e3) =
>   do
>     exprType nEnv tyEnv e1 >>= unify nEnv boolType
>     ty2 <- exprType nEnv tyEnv e2
>     ty3 <- exprType nEnv tyEnv e3
>     unify nEnv ty2 ty3
>     return ty3
> exprType nEnv tyEnv (Case _ as) =
>   do
>     ty <- freshTypeVar
>     mapM_ (altType ty) as
>     return ty
>   where altType ty (Alt _ _ rhs) = rhsType nEnv tyEnv rhs >>= unify nEnv ty

> rhsType :: NewtypeEnv -> ValueEnv -> Rhs -> TyState Type
> rhsType nEnv tyEnv (SimpleRhs _ e _) = exprType nEnv tyEnv e
> rhsType nEnv tyEnv (GuardedRhs es _) =
>   do
>     ty <- freshTypeVar
>     mapM_ (condExprType ty) es
>     return ty
>   where condExprType ty (CondExpr _ _ e) =
>           exprType nEnv tyEnv e >>= unify nEnv ty

\end{verbatim}
In order to avoid name conflicts with non-generalized type variables
in a type we instantiate quantified type variables using non-negative
offsets here.
\begin{verbatim}

> freshTypeVar :: TyState Type
> freshTypeVar = liftM TypeVariable $ liftSt $ updateSt (1 +)

> instType :: Int -> Type -> TyState Type
> instType n ty =
>   do
>     tys <- sequence (replicate n freshTypeVar)
>     return (expandAliasType tys ty)

> instUniv :: TypeScheme -> TyState Type
> instUniv (ForAll n ty) = instType n ty

\end{verbatim}
When unifying two types, the non-generalized variables, i.e.,
variables with negative offsets, must not be substituted. Otherwise,
the unification algorithm is identical to the one used by the type
checker, except that we try expanding newtype constructors when the
types do not match.
\begin{verbatim}

> unify :: NewtypeEnv -> Type -> Type -> TyState ()
> unify nEnv ty1 ty2 = updateSt_ $
>   \theta -> unifyTypes nEnv (subst theta ty1) (subst theta ty2) theta

> unifyList :: NewtypeEnv -> [Type] -> [Type] -> TyState ()
> unifyList nEnv tys1 tys2 = zipWithM_ (unify nEnv) tys1 tys2

> unifyArrow :: NewtypeEnv -> Type -> TyState (Type,Type)
> unifyArrow nEnv ty =
>   do
>     theta <- fetchSt
>     unifyType (subst theta ty)
>   where unifyType (TypeVariable tv)
>           | tv >= 0 =
>               do
>                 ty1 <- freshTypeVar
>                 ty2 <- freshTypeVar
>                 updateSt_ (bindVar tv (TypeArrow ty1 ty2))
>                 return (ty1,ty2)
>         unifyType (TypeArrow ty1 ty2) = return (ty1,ty2)
>         unifyType (TypeConstructor tc tys)
>           | isJust n = unifyType (expandAliasType tys (fromJust n))
>           where n = lookupEnv tc nEnv
>         unifyType ty = internalError ("unifyArrow " ++ showsPrec 11 ty "")

> unifyArrow2 :: NewtypeEnv -> Type -> TyState (Type,Type,Type)
> unifyArrow2 nEnv ty =
>   do
>     (ty1,ty2) <- unifyArrow nEnv ty
>     (ty21,ty22) <- unifyArrow nEnv ty2
>     return (ty1,ty21,ty22)

> unifyTypes :: NewtypeEnv -> Type -> Type -> TypeSubst -> TypeSubst
> unifyTypes _ (TypeVariable tv1) (TypeVariable tv2) theta
>   | tv1 == tv2 = theta
> unifyTypes _ (TypeVariable tv) ty theta
>   | tv >= 0 = bindVar tv ty theta
> unifyTypes _ ty (TypeVariable tv) theta
>   | tv >= 0 = bindVar tv ty theta
> unifyTypes nEnv (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2) theta
>   | tc1 == tc2 = unifyTypeLists nEnv tys1 tys2 theta
> unifyTypes nEnv (TypeConstructor tc tys) ty theta
>   | isJust n = unifyTypes nEnv (expandAliasType tys (fromJust n)) ty theta
>   where n = lookupEnv tc nEnv
> unifyTypes nEnv ty (TypeConstructor tc tys) theta
>   | isJust n = unifyTypes nEnv ty (expandAliasType tys (fromJust n)) theta
>   where n = lookupEnv tc nEnv
> unifyTypes _ (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2) theta
>   | tv1 == tv2 = theta
> unifyTypes nEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) theta =
>   unifyTypeLists nEnv [ty11,ty12] [ty21,ty22] theta
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2) theta
>   | k1 == k2 = theta
> unifyTypes _ ty1 ty2 _ =
>   internalError ("unify: " ++ showsPrec 11 ty1 (' ' : showsPrec 11 ty2 ""))

> unifyTypeLists :: NewtypeEnv -> [Type] -> [Type] -> TypeSubst -> TypeSubst
> unifyTypeLists _ [] [] theta = theta
> unifyTypeLists nEnv (ty1:tys1) (ty2:tys2) theta =
>   unifyTypes nEnv (subst theta' ty1) (subst theta' ty2) theta'
>   where theta' = unifyTypeLists nEnv tys1 tys2 theta

\end{verbatim}
