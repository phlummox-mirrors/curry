% -*- LaTeX -*-
% $Id: IntfSyntaxCheck.lhs 2491 2007-10-12 17:10:28Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfSyntaxCheck.lhs}
\section{Checking Interface Declarations}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler also checks that all type constructor
applications are saturated. Since interface files are closed -- i.e.,
they include declarations of all entities which are defined in other
modules -- the compiler can perform this check without reference to
the global environments.
\begin{verbatim}

> module IntfSyntaxCheck(intfSyntaxCheck) where
> import Base
> import Curry
> import CurryUtils
> import Error
> import IdentInfo
> import List
> import Monad
> import TopEnv

> intfSyntaxCheck :: [IDecl] -> Error [IDecl]
> intfSyntaxCheck ds = mapE (checkIDecl env) ds
>   where env = foldr bindType initTEnv ds

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in interfaces.
\begin{verbatim}

> bindType :: IDecl -> TypeEnv -> TypeEnv
> bindType (IInfixDecl _ _ _ _) = id
> bindType (HidingDataDecl _ tc _) = qualBindTopEnv tc (Data tc [])
> bindType (IDataDecl _ tc _ cs cs') =
>   qualBindTopEnv tc (Data tc (filter (`notElem` cs') (map constr cs)))
> bindType (INewtypeDecl _ tc _ nc) = qualBindTopEnv tc (Data tc [nconstr nc])
> bindType (ITypeDecl _ tc _ _) = qualBindTopEnv tc (Alias tc)
> bindType (IFunctionDecl _ _ _ _) = id

\end{verbatim}
The checks applied to the interface are similar to those performed
during syntax checking of type expressions.
\begin{verbatim}

> checkIDecl :: TypeEnv -> IDecl -> Error IDecl
> checkIDecl _ (IInfixDecl p fix pr op) = return (IInfixDecl p fix pr op)
> checkIDecl env (HidingDataDecl p tc tvs) =
>   checkTypeLhs env p tvs &&>
>   return (HidingDataDecl p tc tvs)
> checkIDecl env (IDataDecl p tc tvs cs cs') =
>   do
>     cs'' <- checkTypeLhs env p tvs &&> mapE (checkConstrDecl env tvs) cs
>     checkHiding p tc (map constr cs) cs'
>     return (IDataDecl p tc tvs cs'' cs')
> checkIDecl env (INewtypeDecl p tc tvs nc) =
>   checkTypeLhs env p tvs &&>
>   liftE (INewtypeDecl p tc tvs) (checkNewConstrDecl env tvs nc)
> checkIDecl env (ITypeDecl p tc tvs ty) =
>   checkTypeLhs env p tvs &&>
>   liftE (ITypeDecl p tc tvs) (checkClosedType env p tvs ty)
> checkIDecl env (IFunctionDecl p f n ty) =
>   maybe (return ()) (checkArity p) n &&>
>   liftE (IFunctionDecl p f n) (checkType env p ty)
>   where checkArity p n =
>           unless (n < toInteger (maxBound::Int)) (errorAt p (arityTooBig n))

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> Error ()
> checkTypeLhs env p tvs =
>   mapE_ (errorAt p . noVariable) (nub tcs) &&>
>   mapE_ (errorAt p . nonLinear . fst) (duplicates tvs')
>   where (tcs,tvs') = partition isTypeConstr tvs
>         isTypeConstr tv = not (null (lookupTopEnv tv env))

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> Error ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   checkTypeLhs env p evs &&>
>   liftE (ConstrDecl p evs c) (mapE (checkClosedType env p tvs') tys)
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   checkTypeLhs env p evs &&>
>   liftE2 (flip (ConOpDecl p evs) op)
>          (checkClosedType env p tvs' ty1)
>          (checkClosedType env p tvs' ty2)
>   where tvs' = evs ++ tvs

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl
>                    -> Error NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p c ty) =
>   liftE (NewConstrDecl p c) (checkClosedType env p tvs ty)

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p ty
>     mapE_ (errorAt p . unboundVariable)
>           (nub (filter (`notElem` tvs) (fv ty')))
>     return ty'

> checkType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkType env p (ConstructorType tc tys) =
>   liftE2 ($)
>          (case qualLookupTopEnv tc env of
>             []
>               | not (isQualified tc) && null tys ->
>                   return (const (VariableType (unqualify tc)))
>               | otherwise -> errorAt p (undefinedType tc)
>             [Data _ _] -> return (ConstructorType tc)
>             [Alias _] -> errorAt p (badTypeSynonym tc)
>             _ -> internalError "checkType")
>          (mapE (checkType env p) tys)
> checkType env p (VariableType tv) =
>   checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) = liftE TupleType (mapE (checkType env p) tys)
> checkType env p (ListType ty) = liftE ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   liftE2 ArrowType (checkType env p ty1) (checkType env p ty2)

> checkHiding :: Position -> QualIdent -> [Ident] -> [Ident] -> Error ()
> checkHiding p tc cs cs' =
>   mapE_ (errorAt p . noConstructor tc) (nub (filter (`notElem` cs) cs'))

\end{verbatim}
\ToDo{Much of the above code could be shared with module
  \texttt{TypeSyntaxCheck}.}

Error messages.
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type " ++ qualName tc

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noVariable :: Ident -> String
> noVariable tv =
>   "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> noConstructor :: QualIdent -> Ident -> String
> noConstructor tc c =
>   "Hidden constructor " ++ name c ++ " is not defined for type " ++
>   qualName tc

> unboundVariable :: Ident -> String
> unboundVariable tv = "Undefined type variable " ++ name tv

> badTypeSynonym :: QualIdent -> String
> badTypeSynonym tc = "Synonym type " ++ qualName tc ++ " in interface"

> arityTooBig :: Integer -> String
> arityTooBig n = "Function arity out of range: " ++ show n

\end{verbatim}
