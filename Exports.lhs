% -*- LaTeX -*-
% $Id: Exports.lhs 1762 2005-09-06 15:02:17Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Exports.lhs}
\section{Creating Interfaces}
After checking a module, the compiler generates the interface's
declarations from the list of exported types and values. If an entity
is imported from another module, its name is qualified with the name
of the module containing its definition. Furthermore, newtypes whose
constructor is not exported are transformed into (abstract) data
types.
\begin{verbatim}

> module Exports(exportInterface) where
> import Base
> import Maybe
> import Set

> exportInterface :: ModuleIdent -> ExportSpec -> PEnv -> TCEnv -> ValueEnv
>                 -> Interface
> exportInterface m (Exporting _ es) pEnv tcEnv tyEnv =
>   Interface m imports (precs ++ hidden ++ ds)
>   where imports = map (IImportDecl noPos) (usedModules ds)
>         precs = foldr (infixDecl m pEnv) [] es
>         hidden = map (hiddenTypeDecl m tcEnv) (hiddenTypes ds)
>         ds = foldr (typeDecl m tcEnv) (foldr (funDecl m tyEnv) [] es) es

> infixDecl :: ModuleIdent -> PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl m pEnv (Export f) ds = iInfixDecl m pEnv f ds
> infixDecl m pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl m pEnv . qualifyLike (fst (splitQualIdent tc))) ds cs
>   where qualifyLike = maybe qualify qualifyWith

> iInfixDecl :: ModuleIdent -> PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl m pEnv op ds =
>   case qualLookupP op pEnv of
>     [] -> ds
>     [PrecInfo _ (OpPrec fix pr)] ->
>       IInfixDecl noPos fix pr (qualUnqualify m op) : ds
>     _ -> internalError "infixDecl"

> typeDecl :: ModuleIdent -> TCEnv -> Export -> [IDecl] -> [IDecl]
> typeDecl _ _ (Export _) ds = ds
> typeDecl m tcEnv (ExportTypeWith tc cs) ds =
>   case qualLookupTC tc tcEnv of
>     [DataType tc n cs'] ->
>       iTypeDecl IDataDecl m tc n (constrs (drop n nameSupply)) : ds
>       where constrs tvs = if null cs then [] else constrDecls m tvs cs cs'
>     [RenamingType tc n (Data c n' ty)]
>       | null cs -> iTypeDecl IDataDecl m tc n [] : ds
>       | otherwise ->
>           iTypeDecl INewtypeDecl m tc n (NewConstrDecl noPos tvs c ty') : ds
>       where tvs = take n' (drop n nameSupply)
>             ty' = fromQualType m ty
>     [AliasType tc n ty] ->
>       iTypeDecl ITypeDecl m tc n (fromQualType m ty) : ds
>     _ -> internalError "typeDecl"

> iTypeDecl :: (Position -> QualIdent -> [Ident] -> a -> IDecl)
>            -> ModuleIdent -> QualIdent -> Int -> a -> IDecl
> iTypeDecl f m tc n = f noPos (qualUnqualify m tc) (take n nameSupply)

> constrDecls :: ModuleIdent -> [Ident] -> [Ident] -> [Maybe (Data [Type])]
>             -> [Maybe ConstrDecl]
> constrDecls m tvs cs = map (>>= constrDecl m tvs)
>   where constrDecl m tvs (Data c n tys)
>           | c `elem` cs =
>               Just (iConstrDecl (take n tvs) c (map (fromQualType m) tys))
>           | otherwise = Nothing

> iConstrDecl :: [Ident] -> Ident -> [TypeExpr] -> ConstrDecl
> iConstrDecl tvs op [ty1,ty2]
>   | isInfixOp op = ConOpDecl noPos tvs ty1 op ty2
> iConstrDecl tvs c tys = ConstrDecl noPos tvs c tys

> funDecl :: ModuleIdent -> ValueEnv -> Export -> [IDecl] -> [IDecl]
> funDecl m tyEnv (Export f) ds =
>   case qualLookupValue f tyEnv of
>     [Value _ (ForAll _ ty)] ->
>       IFunctionDecl noPos (qualUnqualify m f) (fromQualType m ty) : ds
>     _ -> internalError "funDecl"
> funDecl _ _ (ExportTypeWith _ _) ds = ds

\end{verbatim}
The compiler determines the list of imported modules from the set of
module qualifiers that are used in the interface. Careful readers
probably will have noticed that the functions above carefully strip
the module prefix from all entities that are defined in the current
module. Note that the list of modules returned from
\texttt{usedModules} is not necessarily a subset of the modules that
were imported into the current module. This will happen when an
imported module re-exports entities from another module. E.g., given
the three modules
\begin{verbatim}
module A where { data A = A; }
module B(A(..)) where { import A; }
module C where { import B; x = A; }
\end{verbatim}
the interface for module \texttt{C} will import module \texttt{A} but
not module \texttt{B}.
\begin{verbatim}

> usedModules :: [IDecl] -> [ModuleIdent]
> usedModules ds = nub (catMaybes (map modul (foldr identsDecl [] ds)))
>   where nub = toListSet . fromListSet
>         modul = fst . splitQualIdent

> identsDecl :: IDecl -> [QualIdent] -> [QualIdent]
> identsDecl (IDataDecl _ tc _ cs) xs =
>   tc : foldr identsConstrDecl xs (catMaybes cs)
> identsDecl (INewtypeDecl _ tc _ nc) xs = tc : identsNewConstrDecl nc xs
> identsDecl (ITypeDecl _ tc _ ty) xs = tc : identsType ty xs
> identsDecl (IFunctionDecl _ f ty) xs = f : identsType ty xs

> identsConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
> identsConstrDecl (ConstrDecl _ _ _ tys) xs = foldr identsType xs tys
> identsConstrDecl (ConOpDecl _ _ ty1 _ ty2) xs =
>   identsType ty1 (identsType ty2 xs)

> identsNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
> identsNewConstrDecl (NewConstrDecl _ _ _ ty) xs = identsType ty xs

> identsType :: TypeExpr -> [QualIdent] -> [QualIdent]
> identsType (ConstructorType tc tys) xs = tc : foldr identsType xs tys
> identsType (VariableType _) xs = xs
> identsType (TupleType tys) xs = foldr identsType xs tys
> identsType (ListType ty) xs = identsType ty xs
> identsType (ArrowType ty1 ty2) xs = identsType ty1 (identsType ty2 xs)

\end{verbatim}
After the interface declarations have been computed, the compiler
eventually must add hidden (data) type declarations to the interface
for all those types which were used in the interface but not exported
from the current module, so that these type constructors can always be
distinguished from type variables.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tc =
>   case qualLookupTC (qualQualify m tc) tcEnv of
>     [DataType _ n _] -> hidingDataDecl tc n
>     [RenamingType _ n _] -> hidingDataDecl tc n
>     _ ->  internalError "hiddenTypeDecl"
>   where hidingDataDecl tc n =
>           HidingDataDecl noPos (unqualify tc) (take n nameSupply)

> hiddenTypes :: [IDecl] -> [QualIdent]
> hiddenTypes ds = [tc | tc <- toListSet tcs, not (isQualified tc)]
>   where tcs = foldr deleteFromSet (fromListSet (usedTypes ds))
>                     (definedTypes ds)

> usedTypes :: [IDecl] -> [QualIdent]
> usedTypes ds = foldr usedTypesDecl [] ds

> usedTypesDecl :: IDecl -> [QualIdent] -> [QualIdent]
> usedTypesDecl (IDataDecl _ _ _ cs) tcs =
>   foldr usedTypesConstrDecl tcs (catMaybes cs)
> usedTypesDecl (INewtypeDecl _ _ _ nc) tcs = usedTypesNewConstrDecl nc tcs
> usedTypesDecl (ITypeDecl _ _ _ ty) tcs = usedTypesType ty tcs
> usedTypesDecl (IFunctionDecl _ _ ty) tcs = usedTypesType ty tcs

> usedTypesConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
> usedTypesConstrDecl (ConstrDecl _ _ _ tys) tcs = foldr usedTypesType tcs tys
> usedTypesConstrDecl (ConOpDecl _ _ ty1 _ ty2) tcs =
>   usedTypesType ty1 (usedTypesType ty2 tcs)

> usedTypesNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
> usedTypesNewConstrDecl (NewConstrDecl _ _ _ ty) tcs = usedTypesType ty tcs

> usedTypesType :: TypeExpr -> [QualIdent] -> [QualIdent]
> usedTypesType (ConstructorType tc tys) tcs = tc : foldr usedTypesType tcs tys
> usedTypesType (VariableType _) tcs = tcs
> usedTypesType (TupleType tys) tcs = foldr usedTypesType tcs tys
> usedTypesType (ListType ty) tcs = usedTypesType ty tcs
> usedTypesType (ArrowType ty1 ty2) tcs =
>   usedTypesType ty1 (usedTypesType ty2 tcs)

> definedTypes :: [IDecl] -> [QualIdent]
> definedTypes ds = foldr definedType [] ds

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ tc _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _) tcs = tc : tcs
> definedType (IFunctionDecl _ _ _)  tcs = tcs

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> noPos :: Position
> noPos = undefined

\end{verbatim}
