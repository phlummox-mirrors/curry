% -*- LaTeX -*-
% $Id: IntfCheck.lhs 1773 2005-09-22 10:23:22Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfCheck.lhs}
\section{Interface Consistency Checks}
Interface files include declarations of all entities that are exported
by the module, but defined in another module. Since these declarations
can become inconsistent if client modules are not recompiled properly,
the compiler checks that all imported declarations in an interface
agree with their original definitions.

One may ask why we include imported declarations at all, if the
compiler always has to compare those declarations with the original
definitions. The main reason for this is that it helps to avoid
unnecessary recompilations of client modules. As an example, consider
the three modules
\begin{verbatim}
  module A where { data T = C }
  module B(T(..)) where { import A }
  module C where { import B; f = C }
\end{verbatim}
where module \texttt{B} could be considered as a public interface of
module \texttt{A}, which restricts access to type \texttt{A.T} and its
constructor \texttt{C}. The client module \texttt{C} imports this type
via the public interface \texttt{B}. If now module \texttt{A} is
changed by adding a definition of a new global function
\begin{verbatim}
  module A where { data T = C; f = C }
\end{verbatim}
module \texttt{B} must be recompiled because \texttt{A}'s interface is
changed. On the other hand, module \texttt{C} need not be recompiled
because the change in \texttt{A} does not affect \texttt{B}'s
interface. By including the declaration of type \texttt{A.T} in
\texttt{B}'s interface, the compiler can trivially check that
\texttt{B}'s interface remains unchanged and therefore the client
module \texttt{C} is not recompiled.

Another reason for including imported declarations in interfaces is
that the compiler in principle could avoid loading interfaces of
modules that are imported only indirectly, which would save processing
time and allow distributing binary packages of a library with a public
interface module only. However, this has not been implemented yet.
\begin{verbatim}

> module IntfCheck(intfCheck) where
> import Base

> intfCheck :: ModuleIdent -> PEnv -> TCEnv -> ValueEnv -> [IDecl] -> [IDecl]
> intfCheck m pEnv tcEnv tyEnv = map (checkImport m pEnv tcEnv tyEnv)

> checkImport :: ModuleIdent -> PEnv -> TCEnv -> ValueEnv -> IDecl -> IDecl
> checkImport _ pEnv _ _ (IInfixDecl p fix pr op) =
>   checkPrecInfo checkPrec pEnv p op (IInfixDecl p fix pr op)
>   where checkPrec (PrecInfo op' (OpPrec fix' pr')) =
>           op == op' && fix == fix' && pr == pr'
> checkImport _ _ tcEnv _ (HidingDataDecl p tc tvs) =
>   checkTypeInfo "hidden data type" checkData tcEnv p tc
>                 (const (HidingDataDecl p tc tvs)) undefined
>   where checkData (DataType tc' n' _)
>           | tc == tc' && length tvs == n' = Just id
>         checkData (RenamingType tc' n' _)
>           | tc == tc' && length tvs == n' = Just id
>         checkData _ = Nothing
> checkImport m _ tcEnv tyEnv (IDataDecl p tc tvs cs) =
>   checkTypeInfo "data type" checkData tcEnv p tc (IDataDecl p tc tvs) cs
>   where checkData (DataType tc' n' cs')
>           | tc == tc' && length tvs == n' &&
>             (null cs || length cs == length cs') &&
>             and (zipWith isVisible cs cs') =
>               Just (map (fmap (checkConstrImport m tyEnv tc tvs)))
>         checkData (RenamingType tc' n' _)
>           | tc == tc' && length tvs == n' && null cs = Just (const [])
>         checkData _ = Nothing
>         isVisible (Just c) (Just c') = constr c == c'
>         isVisible (Just _) Nothing = False
>         isVisible Nothing _ = True
> checkImport m _ tcEnv tyEnv (INewtypeDecl p tc tvs nc) =
>   checkTypeInfo "newtype" checkNewtype tcEnv p tc (INewtypeDecl p tc tvs) nc
>   where checkNewtype (RenamingType tc' n' nc')
>           | tc == tc' && length tvs == n' && nconstr nc == nc' =
>               Just (checkNewConstrImport m tyEnv tc tvs)
>         checkNewtype _ = Nothing
> checkImport m _ tcEnv _ (ITypeDecl p tc tvs ty) =
>   checkTypeInfo "synonym type" checkType tcEnv p tc (ITypeDecl p tc tvs) ty
>   where checkType (AliasType tc' n' ty')
>           | tc == tc' && length tvs == n' && toQualType m tvs ty == ty' =
>               Just id
>         checkType _ = Nothing
> checkImport m _ _ tyEnv (IFunctionDecl p f ty) =
>   checkValueInfo "function" checkFun tyEnv p f (IFunctionDecl p f ty)
>   where checkFun (Value f' (ForAll _ ty')) =
>           f == f' && toQualType m [] ty == ty'
>         checkFun _ = False

> checkConstrImport :: ModuleIdent -> ValueEnv -> QualIdent -> [Ident]
>                   -> ConstrDecl -> ConstrDecl
> checkConstrImport m tyEnv tc tvs (ConstrDecl p evs c tys) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>                  (ConstrDecl p evs c tys)
>   where qc = qualifyLike tc c
>         checkConstr (DataConstructor c' (ForAllExist _ n' ty')) =
>           qc == c' && length evs == n' &&
>           toQualTypes m tvs tys == arrowArgs ty'
>         checkConstr _ = False
> checkConstrImport m tyEnv tc tvs (ConOpDecl p evs ty1 op ty2) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>                  (ConOpDecl p evs ty1 op ty2)
>   where qc = qualifyLike tc op
>         checkConstr (DataConstructor c' (ForAllExist _ n' ty')) =
>           qc == c' && length evs == n' &&
>           toQualTypes m tvs [ty1,ty2] == arrowArgs ty'
>         checkConstr _ = False

> checkNewConstrImport :: ModuleIdent -> ValueEnv -> QualIdent -> [Ident]
>                      -> NewConstrDecl -> NewConstrDecl
> checkNewConstrImport m tyEnv tc tvs (NewConstrDecl p evs c ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>                  (NewConstrDecl p evs c ty)
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' (ForAllExist _ n' ty')) =
>           qc == c' && length evs == n' &&
>           toQualType m tvs ty == head (arrowArgs ty')
>         checkNewConstr _ = False

> checkPrecInfo :: (PrecInfo -> Bool) -> PEnv -> Position
>               -> QualIdent -> a -> a
> checkPrecInfo check pEnv p op = checkImported checkInfo op
>   where checkInfo m op' =
>           case qualLookupP op pEnv of
>             [] -> errorAt p (noPrecedence m op')
>             [pi]
>               | check pi -> id
>               | otherwise -> errorAt p (importConflict "precedence" m op')
>             _ -> internalError "checkPrecInfo"

> checkTypeInfo :: String -> (TypeInfo -> Maybe (a -> a)) -> TCEnv -> Position
>               -> QualIdent -> (a -> b) -> a -> b
> checkTypeInfo what check tcEnv p tc = checkImported checkInfo tc
>   where checkInfo m tc' =
>           case qualLookupTC tc tcEnv of
>             [] -> errorAt p (notExported what m tc')
>             [ti] ->
>               case check ti of
>                 Just checkConstrs -> \f cs -> f (checkConstrs cs)
>                 Nothing -> errorAt p (importConflict what m tc')
>             _ -> internalError "checkTypeInfo"

> checkValueInfo :: String -> (ValueInfo -> Bool) -> ValueEnv -> Position
>                -> QualIdent -> a -> a
> checkValueInfo what check tyEnv p x = checkImported checkInfo x
>   where checkInfo m x' =
>           case qualLookupValue x tyEnv of
>             [] -> errorAt p (notExported what m x')
>             [vi]
>               | check vi -> id
>               | otherwise -> errorAt p (importConflict what m x')
>             _ -> internalError "checkValueInfo"

> checkImported :: (ModuleIdent -> Ident -> a -> a) -> QualIdent -> a -> a
> checkImported f x =
>   case splitQualIdent x of
>     (Just m,x') -> f m x'
>     (Nothing,_) -> id

\end{verbatim}
Error messages.
\begin{verbatim}

> notExported :: String -> ModuleIdent -> Ident -> String
> notExported what m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not export " ++ what ++ " " ++ name x

> noPrecedence :: ModuleIdent -> Ident -> String
> noPrecedence m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not define a precedence for " ++ name x

> importConflict :: String -> ModuleIdent -> Ident -> String
> importConflict what m x =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of " ++ what ++ " " ++ name x ++
>   " does not match its definition in module " ++ moduleName m

\end{verbatim}
