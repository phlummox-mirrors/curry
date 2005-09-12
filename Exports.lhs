% -*- LaTeX -*-
% $Id: Exports.lhs 1764 2005-09-12 10:37:22Z wlux $
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
>   foldr (iInfixDecl m pEnv . qualifyLike tc) ds cs

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
> usedModules ds = nub (modules ds [])
>   where nub = toListSet . fromListSet

> class HasModule a where
>   modules :: a -> [ModuleIdent] -> [ModuleIdent]

> instance HasModule a => HasModule (Maybe a) where
>   modules = maybe id modules

> instance HasModule a => HasModule [a] where
>   modules xs ms = foldr modules ms xs

> instance HasModule IDecl where
>   modules (IDataDecl _ tc _ cs) = modules tc . modules cs
>   modules (INewtypeDecl _ tc _ nc) = modules tc . modules nc
>   modules (ITypeDecl _ tc _ ty) = modules tc . modules ty
>   modules (IFunctionDecl _ f ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ _ tys) = modules tys
>   modules (ConOpDecl _ _ ty1 _ ty2) = modules ty1 . modules ty2

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ _ ty) = modules ty

> instance HasModule TypeExpr where
>   modules (ConstructorType tc tys) = modules tc . modules tys
>   modules (VariableType _) = id
>   modules (TupleType tys) = modules tys
>   modules (ListType ty) = modules ty
>   modules (ArrowType ty1 ty2) = modules ty1 . modules ty2

> instance HasModule QualIdent where
>   modules = maybe id (:) . fst . splitQualIdent

\end{verbatim}
After the interface declarations have been computed, the compiler
eventually must add hidden (data) type declarations to the interface
for all those types which were used in the interface but not exported
from the current module, so that these type constructors can always be
distinguished from type variables.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> Ident -> IDecl
> hiddenTypeDecl m tcEnv tc =
>   case qualLookupTC (qualifyWith m tc) tcEnv of
>     [DataType _ n _] -> hidingDataDecl tc n
>     [RenamingType _ n _] -> hidingDataDecl tc n
>     _ ->  internalError "hiddenTypeDecl"
>   where hidingDataDecl tc n = HidingDataDecl noPos tc (take n nameSupply)

> hiddenTypes :: [IDecl] -> [Ident]
> hiddenTypes ds = map unqualify (takeWhile (not . isQualified) (toListSet tcs))
>   where tcs = foldr deleteFromSet (fromListSet (usedTypes ds []))
>                     (foldr definedType [] ds)

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ tc _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _) tcs = tc : tcs
> definedType (IFunctionDecl _ _ _)  tcs = tcs

> class HasType a where
>   usedTypes :: a -> [QualIdent] -> [QualIdent]

> instance HasType a => HasType (Maybe a) where
>   usedTypes = maybe id usedTypes

> instance HasType a => HasType [a] where
>   usedTypes xs tcs = foldr usedTypes tcs xs

> instance HasType IDecl where
>   usedTypes (IDataDecl _ _ _ cs) = usedTypes cs
>   usedTypes (INewtypeDecl _ _ _ nc) = usedTypes nc
>   usedTypes (ITypeDecl _ _ _ ty) = usedTypes ty
>   usedTypes (IFunctionDecl _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ _ tys) = usedTypes tys
>   usedTypes (ConOpDecl _ _ ty1 _ ty2) = usedTypes ty1 . usedTypes ty2

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ _ ty) = usedTypes ty

> instance HasType TypeExpr where
>   usedTypes (ConstructorType tc tys) = (tc :) . usedTypes tys
>   usedTypes (VariableType _) = id
>   usedTypes (TupleType tys) = usedTypes tys
>   usedTypes (ListType ty) = usedTypes ty
>   usedTypes (ArrowType ty1 ty2) = usedTypes ty1 . usedTypes ty2

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> noPos :: Position
> noPos = undefined

\end{verbatim}
