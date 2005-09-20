% -*- LaTeX -*-
% $Id: IntfSyntaxCheck.lhs 1769 2005-09-20 14:19:15Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfSyntaxCheck.lhs}
\section{Checking Interface Declarations}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler also checks that all type constructor
applications are saturated.

\ToDo{Since interface files are closed -- i.e., they include
  declarations of all entities, which are defined in another module --
  the compiler should not use the (global) type constructor
  environment. However, this is not possible without including hidden
  type constructors from imported modules in interfaces.}
\begin{verbatim}

> module IntfSyntaxCheck(intfSyntaxCheck) where
> import Base
> import TopEnv

> intfSyntaxCheck :: ModuleIdent -> TCEnv -> [IDecl] -> [IDecl]
> intfSyntaxCheck m tcEnv ds = map (checkIDecl env) ds
>   where env = foldr (bindType m) (fmap typeKind tcEnv) ds

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in interfaces.
\begin{verbatim}

> bindType :: ModuleIdent -> IDecl -> TypeEnv -> TypeEnv
> bindType m (HidingDataDecl _ tc tvs) =
>   bindTop m tc (Data (qualifyWith m tc) (length tvs) [])
> bindType m (IDataDecl _ tc tvs _) =
>   bindTopLocal m tc (Data tc (length tvs) [])
> bindType m (INewtypeDecl _ tc tvs _) =
>   bindTopLocal m tc (Data tc (length tvs) [])
> bindType m (ITypeDecl _ tc tvs ty) =
>   bindTopLocal m tc (Alias tc (length tvs))
> bindType _ _ = id

> bindTopLocal :: ModuleIdent -> QualIdent -> TypeKind -> TypeEnv -> TypeEnv
> bindTopLocal m tc x =
>   case splitQualIdent tc of
>     (Just _,_) -> id
>     (Nothing,tc') -> bindTop m tc' x

\end{verbatim}
The checks applied to the interface are similar to those performed
during syntax checking of type expressions.
\begin{verbatim}

> checkIDecl :: TypeEnv -> IDecl -> IDecl
> checkIDecl env (HidingDataDecl p tc tvs) =
>   HidingDataDecl p tc (checkTypeLhs env p tvs)
> checkIDecl env (IDataDecl p tc tvs cs) =
>   IDataDecl p tc tvs' (map (fmap (checkConstrDecl env tvs')) cs)
>   where tvs' = checkTypeLhs env p tvs
> checkIDecl env (INewtypeDecl p tc tvs nc) =
>   INewtypeDecl p tc tvs' (checkNewConstrDecl env tvs' nc)
>   where tvs' = checkTypeLhs env p tvs
> checkIDecl env (ITypeDecl p tc tvs ty) =
>   ITypeDecl p tc tvs' (checkClosedType env p tvs' ty)
>   where tvs' = checkTypeLhs env p tvs
> checkIDecl env (IFunctionDecl p f ty) =
>   IFunctionDecl p f (checkType env p ty)
> checkIDecl _ d = d

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> [Ident]
> checkTypeLhs env p (tv:tvs)
>   | isTypeConstr tv = errorAt p (noVariable tv)
>   | tv `elem` tvs = errorAt p  (nonLinear tv)
>   | otherwise = tv : checkTypeLhs env p tvs
>   where isTypeConstr tv = not (null (lookupType tv env))
> checkTypeLhs env p [] = []

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs' c (map (checkClosedType env p tvs') tys)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs' (checkClosedType env p tvs' ty1) op
>             (checkClosedType env p tvs' ty2)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl -> NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs' c (checkClosedType env p tvs' ty)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosedType env p tvs ty = checkClosed p tvs (checkType env p ty)

> checkType :: TypeEnv -> Position -> TypeExpr -> TypeExpr
> checkType env p (ConstructorType tc tys) =
>   case qualLookupType tc env of
>     []
>       | not (isQualified tc) && null tys -> VariableType (unqualify tc)
>       | otherwise -> errorAt p (undefinedType tc)
>     [Data _ n _]
>       | n == n' -> ConstructorType tc (map (checkType env p) tys)
>       | otherwise -> errorAt p (wrongArity tc n n')
>       where n' = length tys
>     [Alias _ _] -> errorAt p (badTypeSynonym tc)
>     _ -> internalError "checkType"
> checkType env p (VariableType tv) =
>   checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) = TupleType (map (checkType env p) tys)
> checkType env p (ListType ty) = ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   ArrowType (checkType env p ty1) (checkType env p ty2)

> checkClosed :: Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosed p tvs (ConstructorType tc tys) =
>   ConstructorType tc (map (checkClosed p tvs) tys)
> checkClosed p tvs (VariableType tv)
>   | tv `notElem` tvs = errorAt p (unboundVariable tv)
>   | otherwise = VariableType tv
> checkClosed p tvs (TupleType tys) =
>   TupleType (map (checkClosed p tvs) tys)
> checkClosed p tvs (ListType ty) =
>   ListType (checkClosed p tvs ty)
> checkClosed p tvs (ArrowType ty1 ty2) =
>   ArrowType (checkClosed p tvs ty1) (checkClosed p tvs ty2)

\end{verbatim}
\ToDo{Much of the above code could be shared with module
  \texttt{TypeSyntaxCheck}.}

Error messages.
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type constructor " ++ qualName tc

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noVariable :: Ident -> String
> noVariable tv =
>   "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity tc arity argc =
>   "Type constructor " ++ qualName tc ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> unboundVariable :: Ident -> String
> unboundVariable tv = "Unbound type variable " ++ name tv

> badTypeSynonym :: QualIdent -> String
> badTypeSynonym tc = "Synonym type " ++ qualName tc ++ " in interface"

\end{verbatim}
