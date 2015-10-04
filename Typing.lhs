% -*- LaTeX -*-
% $Id: Typing.lhs 3177 2015-10-04 08:04:49Z wlux $
%
% Copyright (c) 2003-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..), etaType, withType, argumentTypes, bindDecls,
>               bindLhs, bindTerms, bindTerm, declVars, termVars) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import Maybe
> import PredefTypes
> import TopEnv
> import Types
> import TypeInfo
> import TypeSubst
> import ValueInfo
> import Utils

\end{verbatim}
After the compiler has attributed patterns and expressions with type
information during type inference, it is straightforward to recompute
the type of every pattern and expression. Since all annotated types
are monomorphic, there is no need to instantiate any variables or
perform any (non-trivial) unifications.
\begin{verbatim}

> class Typeable a where
>   typeOf :: a -> Type

> instance Typeable Type where
>   typeOf = id

> instance Typeable a => Typeable (ConstrTerm a) where
>   typeOf (LiteralPattern a _) = typeOf a
>   typeOf (NegativePattern a _ _) = typeOf a
>   typeOf (VariablePattern a _) = typeOf a
>   typeOf (ConstructorPattern a _ _) = typeOf a
>   typeOf (FunctionPattern a _ _) = typeOf a
>   typeOf (InfixPattern a _ _ _) = typeOf a
>   typeOf (ParenPattern t) = typeOf t
>   typeOf (RecordPattern a _ _) = typeOf a
>   typeOf (TuplePattern ts) = tupleType (map typeOf ts)
>   typeOf (ListPattern a _) = typeOf a
>   typeOf (AsPattern _ t) = typeOf t
>   typeOf (LazyPattern t) = typeOf t

> instance Typeable a => Typeable (Expression a) where
>   typeOf (Literal a _) = typeOf a
>   typeOf (Variable a _) = typeOf a
>   typeOf (Constructor a _) = typeOf a
>   typeOf (Paren e) = typeOf e
>   typeOf (Typed e _) = typeOf e
>   typeOf (Record a _ _) = typeOf a
>   typeOf (RecordUpdate e _) = typeOf e
>   typeOf (Tuple es) = tupleType (map typeOf es)
>   typeOf (List a _) = typeOf a
>   typeOf (ListCompr e _) = listType (typeOf e)
>   typeOf (EnumFrom e) = listType (typeOf e)
>   typeOf (EnumFromThen e _) = listType (typeOf e)
>   typeOf (EnumFromTo e _) = listType (typeOf e)
>   typeOf (EnumFromThenTo e _ _) = listType (typeOf e)
>   typeOf (UnaryMinus _ e) = typeOf e
>   typeOf (Apply e _) =
>     case typeOf e of
>       TypeArrow _ ty -> ty
>       _ -> internalError "typeOf (Apply)"
>   typeOf (InfixApply _ op _) =
>     case typeOf (infixOp op) of
>       TypeArrow _ (TypeArrow _ ty) -> ty
>       _ -> internalError "typeOf (InfixApply)"
>   typeOf (LeftSection _ op) =
>     case typeOf (infixOp op) of
>       TypeArrow _ ty -> ty
>       _ -> internalError "typeOf (LeftSection)"
>   typeOf (RightSection op _) =
>     case typeOf (infixOp op) of
>       TypeArrow ty1 (TypeArrow _ ty2) -> TypeArrow ty1 ty2
>       _ -> internalError "typeOf (RightSection)"
>   typeOf (Lambda _ ts e) = foldr (TypeArrow . typeOf) (typeOf e) ts
>   typeOf (Let _ e) = typeOf e
>   typeOf (Do _ e) = typeOf e
>   typeOf (IfThenElse _ e _) = typeOf e
>   typeOf (Case _ as) = head [typeOf rhs | Alt _ _ rhs <- as]
>   typeOf (Fcase _ as) = head [typeOf rhs | Alt _ _ rhs <- as]

> instance Typeable a => Typeable (Rhs a) where
>   typeOf (SimpleRhs _ e _) = typeOf e
>   typeOf (GuardedRhs es _) = head [typeOf e | CondExpr _ _ e <- es]

\end{verbatim}
After desugaring, the compiler removes newtype constructors and
changes renaming types into type synonyms. However, in contrast to
type synonyms, renaming types can be recursive. Therefore, we expand
type synonyms only lazily during program transformations. This may be
necessary, e.g., when a function is $\eta$-expanded and its result
type is a renaming type whose representation type is a function type:
\begin{verbatim}
  newtype ST s a = ST (\s -> (a,s))
  returnST x = ST (\s -> (x,s))
\end{verbatim}
Here \texttt{returnST} can be $\eta$-expanded after removing the
newtype constructor \texttt{ST} and its type must be changed from
\texttt{a -> ST s a} into \texttt{a -> s -> (a,s)}.
\begin{verbatim}

> etaType :: TCEnv -> Int -> Type -> Type
> etaType _ 0 ty = ty
> etaType tcEnv n (TypeArrow ty1 ty2) =
>   TypeArrow ty1 (etaType tcEnv (n - 1) ty2)
> etaType tcEnv n (TypeConstructor tc tys) =
>   maybe (TypeConstructor tc tys) (etaType tcEnv n) (expandType tcEnv tc tys)
> etaType _ _ ty = ty

\end{verbatim}
When inlining variable and function definitions, the compiler must
eventually update the type annotations of the inlined expression. To
that end, the variable or function's annotated type and the type of
the inlined expression must be unified. Since the program is type
correct, this unification is just a simple one way matching where we
only need to match the type variables in the inlined expression's type
with the corresponding types in the variable or function's annotated
type. However, we may need to expand type synonyms stemming from
removed newtypes.

\ToDo{We would like to use the more general type signature
  \texttt{(Functor f,Typeable (f Type)) => TCEnv -> Type -> f Type ->
    f Type} for \texttt{withType}. Unfortunately, nhc98 at present
  supports only simple class constraints, i.e., constraints where the
  constrained type is a type variable.}
\begin{verbatim}

> withType :: TCEnv -> Type -> Expression Type -> Expression Type
> withType tcEnv ty x = fmap (subst (matchType tcEnv (typeOf x) ty idSubst)) x

> matchType :: TCEnv -> Type -> Type -> TypeSubst -> TypeSubst
> matchType _ (TypeVariable tv) ty
>   | ty == TypeVariable tv = id
>   | otherwise = bindSubst tv ty
> matchType tcEnv (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = matchTypes tcEnv tys1 tys2
> matchType tcEnv (TypeConstructor tc tys) ty
>   | isJust ty' = matchType tcEnv (fromJust ty') ty
>   where ty' = expandType tcEnv tc tys
> matchType tcEnv ty (TypeConstructor tc tys)
>   | isJust ty' = matchType tcEnv ty (fromJust ty')
>   where ty' = expandType tcEnv tc tys
> matchType _ (TypeConstrained _ tv1) (TypeConstrained _ tv2)
>   | tv1 == tv2 = id
> matchType tcEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   matchType tcEnv ty11 ty21 . matchType tcEnv ty12 ty22
> matchType _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = id
> matchType _ ty1 ty2 =
>   internalError ("matchType " ++ showsPrec 11 ty1 (' ' : showsPrec 11 ty2 ""))

> matchTypes :: TCEnv -> [Type] -> [Type] -> TypeSubst -> TypeSubst
> matchTypes _ [] [] = id
> matchTypes tcEnv (ty1:tys1) (ty2:tys2) =
>   matchType tcEnv ty1 ty2 . matchTypes tcEnv tys1 tys2

> expandType :: TCEnv -> QualIdent -> [Type] -> Maybe Type
> expandType tcEnv tc tys = fmap (instTypeScheme tys) (typeAlias tc tcEnv)

\end{verbatim}
The function \texttt{argumentTypes} returns the labels and the
argument types of a data constructor instantiated at a particular
type. This function is useful for desugaring record patterns and
expressions, where the compiler must compute the types of the omitted
arguments. Since the type annotation of record patterns and
expressions applies to the pattern or expression as a whole, the
instance type is unified with the constructor's result type and the
resulting substitution is applied to all argument types. Note that
this is sound because record fields cannot have existentially
quantified types and therefore all type variables appearing in their
types occur in the constructor's result type as well.
\begin{verbatim}

> argumentTypes :: TCEnv -> Type -> QualIdent -> ValueEnv -> ([Ident],[Type])
> argumentTypes tcEnv ty c tyEnv =
>   (ls,map (subst (matchType tcEnv ty0 ty idSubst)) tys)
>   where (ls,ForAll _ ty') = conType c tyEnv
>         (tys,ty0) = arrowUnapply ty'

\end{verbatim}
The functions \texttt{bindDecls}, \texttt{bindDecl}, \texttt{bindLhs},
\texttt{bindTerm} augment the type environment with the types of the
entities defined in local declaration groups and terms, respectively,
using the types from their type attributes.
\begin{verbatim}

> bindDecls :: [Decl Type] -> ValueEnv -> ValueEnv
> bindDecls ds tyEnv = foldr bindDecl tyEnv ds

> bindDecl :: Decl Type -> ValueEnv -> ValueEnv
> bindDecl d tyEnv = bindLocalVars (filter (unbound tyEnv) (declVars d)) tyEnv
>   where unbound tyEnv v = null (lookupTopEnv (fst3 v) tyEnv)

> bindLhs :: Lhs Type -> ValueEnv -> ValueEnv
> bindLhs = bindTerms . snd . flatLhs

> bindTerms :: [ConstrTerm Type] -> ValueEnv -> ValueEnv
> bindTerms ts tyEnv = foldr bindTerm tyEnv ts

> bindTerm :: ConstrTerm Type -> ValueEnv -> ValueEnv
> bindTerm t tyEnv = bindLocalVars (filter (unbound tyEnv) (termVars t)) tyEnv
>   where unbound tyEnv v = null (lookupTopEnv (fst3 v) tyEnv)

> declVars :: Decl Type -> [(Ident,Int,Type)]
> declVars (InfixDecl _ _ _ _) = []
> declVars (TypeSig _ _ _) = []
> declVars (FunctionDecl _ ty f eqs) = [(f,eqnArity (head eqs),ty)]
> declVars (ForeignDecl _ _ ty f _) = [(f,foreignArity ty,ty)]
> declVars (PatternDecl _ t _) = termVars t
> declVars (FreeDecl _ vs) = [(v,0,ty) | FreeVar ty v <- vs]
> declVars (TrustAnnot _ _ _) = []

> termVars :: ConstrTerm Type -> [(Ident,Int,Type)]
> termVars (LiteralPattern _ _) = []
> termVars (NegativePattern _ _ _) = []
> termVars (VariablePattern ty v) = [(v,0,ty)]
> termVars (ConstructorPattern _ _ ts) = concatMap termVars ts
> termVars (FunctionPattern _ _ ts) = concatMap termVars ts
> termVars (InfixPattern _ t1 _ t2) = termVars t1 ++ termVars t2
> termVars (ParenPattern t) = termVars t
> termVars (RecordPattern _ _ fs) = concat [termVars t | Field _ t <- fs]
> termVars (TuplePattern ts) = concatMap termVars ts
> termVars (ListPattern _ ts) = concatMap termVars ts
> termVars (AsPattern v t) = (v,0,typeOf t) : termVars t
> termVars (LazyPattern t) = termVars t

\end{verbatim}
