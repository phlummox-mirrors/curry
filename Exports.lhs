% -*- LaTeX -*-
% $Id: Exports.lhs 2498 2007-10-14 13:16:00Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
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
> import Curry
> import CurryUtils
> import List
> import Monad
> import PrecInfo
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

> exportInterface :: Module a -> PEnv -> TCEnv -> ValueEnv -> Interface
> exportInterface (Module m (Just (Exporting _ es)) _ _) pEnv tcEnv tyEnv =
>   Interface m imports (precs ++ hidden ++ ds)
>   where tvs = nameSupply
>         imports = map (IImportDecl noPos) (usedModules ds)
>         precs = foldr (infixDecl m pEnv) [] es
>         hidden = map (hiddenTypeDecl m tcEnv tvs) (hiddenTypes ds)
>         ds =
>           foldr (typeDecl m tcEnv tyEnv tvs)
>                 (foldr (valueDecl m tcEnv tyEnv tvs) [] es)
>                 es

> infixDecl :: ModuleIdent -> PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl m pEnv (Export f) ds = iInfixDecl m pEnv f ds
> infixDecl m pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl m pEnv . qualifyLike tc) ds cs

> iInfixDecl :: ModuleIdent -> PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl m pEnv op ds =
>   case qualLookupTopEnv op pEnv of
>     [] -> ds
>     [PrecInfo _ (OpPrec fix pr)] ->
>       IInfixDecl noPos fix pr (qualUnqualify m op) : ds
>     _ -> internalError "infixDecl"

> typeDecl :: ModuleIdent -> TCEnv -> ValueEnv -> [Ident] -> Export -> [IDecl]
>          -> [IDecl]
> typeDecl _ _ _ _ (Export _) ds = ds
> typeDecl m tcEnv tyEnv tvs (ExportTypeWith tc xs) ds =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ n cs] -> iTypeDecl IDataDecl m tc tvs n constrs xs' : ds
>       where constrs = guard vis >> cs'
>             xs' = guard vis >> filter (`notElem` xs) (cs ++ ls)
>             cs' = map (constrDecl tcEnv tyEnv xs tc tvs n) cs
>             ls = nub (concatMap labels cs')
>             vis = not (null xs)
>     [RenamingType _ n c] -> iTypeDecl INewtypeDecl m tc tvs n nc xs' : ds
>       where nc = newConstrDecl tcEnv tyEnv xs tc tvs c
>             xs' = [c | c `notElem` xs]
>     [AliasType _ n ty] ->
>       iTypeDecl ITypeDecl m tc tvs n (fromType tcEnv tvs ty) : ds
>     _ -> internalError "typeDecl"

> iTypeDecl :: (Position -> QualIdent -> [Ident] -> a) -> ModuleIdent
>           -> QualIdent -> [Ident] -> Int -> a
> iTypeDecl f m tc tvs n = f noPos (qualUnqualify m tc) (take n tvs)

> constrDecl :: TCEnv -> ValueEnv -> [Ident] -> QualIdent -> [Ident] -> Int
>            -> Ident -> ConstrDecl
> constrDecl tcEnv tyEnv xs tc tvs n c
>   | any (`elem` xs) ls = RecordDecl noPos evs c fs
>   | otherwise = ConstrDecl noPos evs c tys
>   where evs = drop n (take n' tvs)
>         (ls,ForAll n' ty) = conType (qualifyLike tc c) tyEnv
>         tys = map (fromType tcEnv tvs) (arrowArgs ty)
>         fs = zipWith (FieldDecl noPos . return) ls tys

> newConstrDecl :: TCEnv -> ValueEnv -> [Ident] -> QualIdent -> [Ident] -> Ident
>               -> NewConstrDecl
> newConstrDecl tcEnv tyEnv xs tc tvs c
>   | l `elem` xs = NewRecordDecl noPos c l ty'
>   | otherwise = NewConstrDecl noPos c ty'
>   where (l:_,ForAll _ ty) = conType (qualifyLike tc c) tyEnv
>         ty' = fromType tcEnv tvs (head (arrowArgs ty))

> valueDecl :: ModuleIdent -> TCEnv -> ValueEnv -> [Ident] -> Export -> [IDecl]
>           -> [IDecl]
> valueDecl m tcEnv tyEnv tvs (Export f) ds =
>   IFunctionDecl noPos (qualUnqualify m f) n' (fromType tcEnv tvs ty) : ds
>   where n = arity f tyEnv
>         n' = if arrowArity ty == n then Nothing else Just (toInteger n)
>         ForAll _ ty = funType f tyEnv
> valueDecl _ _ _ _ (ExportTypeWith _ _) ds = ds

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
>   modules (IDataDecl _ tc _ cs _) = modules tc . modules cs
>   modules (INewtypeDecl _ tc _ nc _) = modules tc . modules nc
>   modules (ITypeDecl _ tc _ ty) = modules tc . modules ty
>   modules (IFunctionDecl _ f _ ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ _ tys) = modules tys
>   modules (ConOpDecl _ _ ty1 _ ty2) = modules ty1 . modules ty2
>   modules (RecordDecl _ _ _ fs) = modules fs

> instance HasModule FieldDecl where
>   modules (FieldDecl _ _ ty) = modules ty

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ ty) = modules ty
>   modules (NewRecordDecl _ _ _ ty) = modules ty

> instance HasModule TypeExpr where
>   modules (ConstructorType tc tys) = modules tc . modules tys
>   modules (VariableType _) = id
>   modules (TupleType tys) = modules tys
>   modules (ListType ty) = modules ty
>   modules (ArrowType ty1 ty2) = modules ty1 . modules ty2

> instance HasModule QualIdent where
>   modules = maybe id (:) . fst . splitQualIdent

\end{verbatim}
After the interface declarations have been computed, the compiler adds
hidden (data) type declarations to the interface for all types which
were used in the interface but are not exported from it. This is
necessary in order to distinguish type constructors and type
variables. Furthermore, by including hidden types in interfaces the
compiler can check them without loading the imported modules.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> [Ident] -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tvs tc = HidingDataDecl noPos tc (take n tvs)
>   where n = constrKind (qualQualify m tc) tcEnv

> hiddenTypes :: [IDecl] -> [QualIdent]
> hiddenTypes ds =
>   filter (not . isPrimTypeId) (toListSet (foldr deleteFromSet used defd))
>   where used = fromListSet (usedTypes ds [])
>         defd = foldr definedType [] ds

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ tc _ _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _) tcs = tc : tcs
> definedType (IFunctionDecl _ _ _ _) tcs = tcs

> class HasType a where
>   usedTypes :: a -> [QualIdent] -> [QualIdent]

> instance HasType a => HasType (Maybe a) where
>   usedTypes = maybe id usedTypes

> instance HasType a => HasType [a] where
>   usedTypes xs tcs = foldr usedTypes tcs xs

> instance HasType IDecl where
>   usedTypes (IDataDecl _ _ _ cs _) = usedTypes cs
>   usedTypes (INewtypeDecl _ _ _ nc _) = usedTypes nc
>   usedTypes (ITypeDecl _ _ _ ty) = usedTypes ty
>   usedTypes (IFunctionDecl _ _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ _ tys) = usedTypes tys
>   usedTypes (ConOpDecl _ _ ty1 _ ty2) = usedTypes ty1 . usedTypes ty2
>   usedTypes (RecordDecl _ _ _ fs) = usedTypes fs

> instance HasType FieldDecl where
>   usedTypes (FieldDecl _ _ ty) = usedTypes ty

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ ty) = usedTypes ty
>   usedTypes (NewRecordDecl _ _ _ ty) = usedTypes ty

> instance HasType TypeExpr where
>   usedTypes (ConstructorType tc tys) = (tc :) . usedTypes tys
>   usedTypes (VariableType _) = id
>   usedTypes (TupleType tys) = usedTypes tys
>   usedTypes (ListType ty) = usedTypes ty
>   usedTypes (ArrowType ty1 ty2) = usedTypes ty1 . usedTypes ty2

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> noPos :: Position
> noPos = undefined

\end{verbatim}
