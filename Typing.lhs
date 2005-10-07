% -*- LaTeX -*-
% $Id: Typing.lhs 1785 2005-10-07 11:13:16Z wlux $
%
% Copyright (c) 2003-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..)) where
> import Base
> import TypeSubst
> import Combined
> import Monad
> import Utils

\end{verbatim}
During the transformation of the Curry source code into the
intermediate language, the compiler has to recompute the type of
expressions. This is simpler than type checking because the types of
all variables are known. Still the compiler must handle polymorphic
types of variables and their instantiation. Fortunately, all
monomorphic types entered into the type environment by the type
inferencer have negative offsets. As all types computed by
\texttt{typeOf} are also monomorphic, we can use positive offsets for
the instantiation of type schemes here without risk of name conflicts.

\ToDo{When computing the type of an expression with a type signature
make use of the annotation instead of recomputing its type. In order
to do this we must either ensure that the type is properly qualified
or we need access to the type constructor environment.}
\begin{verbatim}

> type TyState a = StateT TypeSubst (StateT Int Id) a

> run :: TyState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m idSubst) 0

> class Typeable a where
>   typeOf :: ValueEnv -> a -> Type

> instance Typeable Ident where
>   typeOf = computeType identType

> instance Typeable ConstrTerm where
>   typeOf = computeType argType

> instance Typeable Expression where
>   typeOf = computeType exprType

> instance Typeable Rhs where
>   typeOf = computeType rhsType

> computeType :: (ValueEnv -> a -> TyState Type) -> ValueEnv -> a -> Type
> computeType f tyEnv x = normalize (run doComputeType tyEnv)
>  where doComputeType =
>          do
>            ty <- f tyEnv x
>            theta <- fetchSt
>            return (subst theta ty)

> identType :: ValueEnv -> Ident -> TyState Type
> identType tyEnv x = instUniv (varType x tyEnv)

> litType :: ValueEnv -> Literal -> TyState Type
> litType _ (Char _) = return charType
> litType tyEnv (Int v _) = identType tyEnv v
> litType _ (Float _) = return floatType
> litType _ (String _) = return stringType

> argType :: ValueEnv -> ConstrTerm -> TyState Type
> argType tyEnv (LiteralPattern l) = litType tyEnv l
> argType tyEnv (NegativePattern _ l) = litType tyEnv l
> argType tyEnv (VariablePattern v) = identType tyEnv v
> argType tyEnv (ConstructorPattern c ts) =
>   do
>     (tys,ty) <- liftM arrowUnapply (instUnivExist (constrType c tyEnv))
>     tys' <- mapM (argType tyEnv) ts
>     unifyList tys tys'
>     return ty
> argType tyEnv (InfixPattern t1 op t2) =
>   argType tyEnv (ConstructorPattern op [t1,t2])
> argType tyEnv (ParenPattern t) = argType tyEnv t
> argType tyEnv (TuplePattern ts) = liftM tupleType (mapM (argType tyEnv) ts)
> argType tyEnv (ListPattern ts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (elemType ty) ts
>     return (listType ty)
>   where elemType ty t = argType tyEnv t >>= unify ty
> argType tyEnv (AsPattern v _) = argType tyEnv (VariablePattern v)
> argType tyEnv (LazyPattern t) = argType tyEnv t

> exprType :: ValueEnv -> Expression -> TyState Type
> exprType tyEnv (Literal l) = litType tyEnv l
> exprType tyEnv (Variable v) = instUniv (funType v tyEnv)
> exprType tyEnv (Constructor c) = instUnivExist (constrType c tyEnv)
> exprType tyEnv (Typed e _) = exprType tyEnv e
> exprType tyEnv (Paren e) = exprType tyEnv e
> exprType tyEnv (Tuple es) = liftM tupleType (mapM (exprType tyEnv) es)
> exprType tyEnv (List es) =
>   do
>     ty <- freshTypeVar
>     mapM_ (elemType ty) es
>     return (listType ty)
>   where elemType ty e = exprType tyEnv e >>= unify ty
> exprType tyEnv (ListCompr e _) = liftM listType (exprType tyEnv e)
> exprType tyEnv (EnumFrom _) = return (listType intType)
> exprType tyEnv (EnumFromThen _ _) = return (listType intType)
> exprType tyEnv (EnumFromTo _ _) = return (listType intType)
> exprType tyEnv (EnumFromThenTo _ _ _) = return (listType intType)
> exprType tyEnv (UnaryMinus _ e) = exprType tyEnv e
> exprType tyEnv (Apply e1 e2) =
>   do
>     (ty1,ty2) <- exprType tyEnv e1 >>= unifyArrow
>     exprType tyEnv e2 >>= unify ty1
>     return ty2
> exprType tyEnv (InfixApply e1 op e2) =
>   do
>     (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
>     exprType tyEnv e1 >>= unify ty1
>     exprType tyEnv e2 >>= unify ty2
>     return ty3
> exprType tyEnv (LeftSection e op) =
>   do
>     (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
>     exprType tyEnv e >>= unify ty1
>     return (TypeArrow ty2 ty3)
> exprType tyEnv (RightSection op e) =
>   do
>     (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
>     exprType tyEnv e >>= unify ty2
>     return (TypeArrow ty1 ty3)
> exprType tyEnv (Lambda args e) =
>   do
>     tys <- mapM (argType tyEnv) args
>     ty <- exprType tyEnv e
>     return (foldr TypeArrow ty tys)
> exprType tyEnv (Let _ e) = exprType tyEnv e
> exprType tyEnv (Do _ e) = exprType tyEnv e
> exprType tyEnv (IfThenElse e1 e2 e3) =
>   do
>     exprType tyEnv e1 >>= unify boolType
>     ty2 <- exprType tyEnv e2
>     ty3 <- exprType tyEnv e3
>     unify ty2 ty3
>     return ty3
> exprType tyEnv (Case _ alts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (altType ty) alts
>     return ty
>   where altType ty (Alt _ _ rhs) = rhsType tyEnv rhs >>= unify ty

> rhsType :: ValueEnv -> Rhs -> TyState Type
> rhsType tyEnv (SimpleRhs _ e _) = exprType tyEnv e
> rhsType tyEnv (GuardedRhs es _) =
>   do
>     ty <- freshTypeVar
>     mapM_ (condExprType ty) es
>     return ty
>   where condExprType ty (CondExpr _ _ e) = exprType tyEnv e >>= unify ty

\end{verbatim}
In order to avoid name conflicts with non-generalized type variables
in a type we instantiate quantified type variables using positive
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

> instUnivExist :: ExistTypeScheme -> TyState Type
> instUnivExist (ForAllExist n n' ty) = instType (n + n') ty

\end{verbatim}
When unifying two types, the non-generalized variables, i.e.,
variables with negative offsets, must not be substituted. Otherwise,
the unification algorithm is identical to the one used by the type
checker.
\begin{verbatim}

> unify :: Type -> Type -> TyState ()
> unify ty1 ty2 =
>   updateSt_ (\theta -> unifyTypes (subst theta ty1) (subst theta ty2) theta)

> unifyList :: [Type] -> [Type] -> TyState ()
> unifyList tys1 tys2 = sequence_ (zipWith unify tys1 tys2)

> unifyArrow :: Type -> TyState (Type,Type)
> unifyArrow ty =
>   do
>     theta <- fetchSt
>     case subst theta ty of
>       TypeVariable tv
>         | tv >= 0 ->
>             do
>               ty1 <- freshTypeVar
>               ty2 <- freshTypeVar
>               updateSt_ (bindVar tv (TypeArrow ty1 ty2))
>               return (ty1,ty2)
>       TypeArrow ty1 ty2 -> return (ty1,ty2)
>       ty' -> internalError ("unifyArrow (" ++ show ty' ++ ")")

> unifyArrow2 :: Type -> TyState (Type,Type,Type)
> unifyArrow2 ty =
>   do
>     (ty1,ty2) <- unifyArrow ty
>     (ty21,ty22) <- unifyArrow ty2
>     return (ty1,ty21,ty22)

> unifyTypes :: Type -> Type -> TypeSubst -> TypeSubst
> unifyTypes (TypeVariable tv1) (TypeVariable tv2) theta
>   | tv1 == tv2 = theta
> unifyTypes (TypeVariable tv) ty theta
>   | tv >= 0 = bindVar tv ty theta
> unifyTypes ty (TypeVariable tv) theta
>   | tv >= 0 = bindVar tv ty theta
> unifyTypes (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2) theta
>   | tc1 == tc2 = unifyTypeLists tys1 tys2 theta
> unifyTypes (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2) theta
>   | tv1 == tv2 = theta
> unifyTypes (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) theta =
>   unifyTypeLists [ty11,ty12] [ty21,ty22] theta
> unifyTypes (TypeSkolem k1) (TypeSkolem k2) theta
>   | k1 == k2 = theta
> unifyTypes ty1 ty2 _ =
>   internalError ("unify: (" ++ show ty1 ++ ") (" ++ show ty2 ++ ")")

> unifyTypeLists :: [Type] -> [Type] -> TypeSubst -> TypeSubst
> unifyTypeLists [] [] theta = theta
> unifyTypeLists (ty1:tys1) (ty2:tys2) theta =
>   unifyTypes (subst theta' ty1) (subst theta' ty2) theta'
>   where theta' = unifyTypeLists tys1 tys2 theta

\end{verbatim}
The functions \texttt{constrType}, \texttt{varType}, and
\texttt{funType} are used for computing the type of constructors,
pattern variables, and variables.

\ToDo{These functions should be shared with the type checker.}
\begin{verbatim}

> constrType :: QualIdent -> ValueEnv -> ExistTypeScheme
> constrType c tyEnv =
>   case qualLookupValue c tyEnv of
>     [DataConstructor _ sigma] -> sigma
>     [NewtypeConstructor _ sigma] -> sigma
>     _ -> internalError ("constrType " ++ show c)

> varType :: Ident -> ValueEnv -> TypeScheme
> varType v tyEnv =
>   case lookupValue v tyEnv of
>     [Value _ sigma] -> sigma
>     _ -> internalError ("varType " ++ show v)

> funType :: QualIdent -> ValueEnv -> TypeScheme
> funType f tyEnv =
>   case qualLookupValue f tyEnv of
>     [Value _ sigma] -> sigma
>     _ -> internalError ("funType " ++ show f)

\end{verbatim}
