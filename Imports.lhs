% -*- LaTeX -*-
% $Id: Imports.lhs 2892 2009-08-07 13:45:11Z wlux $
%
% Copyright (c) 2000-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Imports.lhs}
\section{Importing Interfaces}
This module provides a few functions which can be used to import
interfaces into the current module.
\begin{verbatim}

> module Imports(importIdents,importInterface,importInterfaceIntf,
>                importUnifyData) where
> import Base
> import Curry
> import CurryUtils
> import IdentInfo
> import List
> import Map
> import Maybe
> import PrecInfo
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

\end{verbatim}
When an interface is imported into a module, the compiler must respect
the import specifications in the import declaration. If an import
specification is present, only those entities which are included in
the specification or not hidden by it, respectively, are added to the
global environments. If the qualified flag is present, only a
qualified import is performed. Otherwise, both a qualified and an
unqualified import are performed.
\begin{verbatim}

> importIdents :: ModuleIdent -> Bool -> Maybe ImportSpec -> (TypeEnv,FunEnv)
>              -> Interface -> (TypeEnv,FunEnv)
> importIdents m q is (tEnv,vEnv) (Interface _ _ ds) =
>   (importEntities tidents m q ts (importData vs) ds tEnv,
>    importEntities vidents m q vs id ds vEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,ValueEnv)
> importInterface m q is (pEnv,tcEnv,tyEnv) (Interface _ _ ds) =
>   (importEntities precs m q vs id ds pEnv,
>    importEntities types m q ts id ds tcEnv,
>    importEntities values m q vs id ds tyEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> isVisible :: (Import -> Set Ident -> Set Ident) -> Maybe ImportSpec
>           -> Ident -> Bool
> isVisible add (Just (Importing _ xs)) = (`elemSet` foldr add zeroSet xs)
> isVisible add (Just (Hiding _ xs)) = (`notElemSet` foldr add zeroSet xs)
> isVisible _ Nothing = const True

> importEntities :: Entity a => (IDecl -> [a]) -> ModuleIdent -> Bool
>                -> (Ident -> Bool) -> (a -> a) -> [IDecl]
>                -> TopEnv a -> TopEnv a
> importEntities ents m q isVisible f ds env =
>   foldr (uncurry (importTopEnv q m)) env
>         [(x,f y) | y <- concatMap ents ds,
>                    let x = unqualify (origName y), isVisible x]

> importData :: (Ident -> Bool) -> TypeKind -> TypeKind
> importData isVisible (Data tc xs) = Data tc (filter isVisible xs)
> importData _ (Alias tc) = Alias tc

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because only a qualified import is necessary and there are no import
restrictions. Besides entities defined in the interface's module, we
must also import entities that are reexported from other modules
provided that the compiler did not load the respective interfaces.

Note that the first argument of \texttt{importInterfaceIntf} is the
list of names of the modules whose interfaces have been read by the
compiler. Obviously, this must include the current interface's module
name.
\begin{verbatim}

> importInterfaceIntf :: [ModuleIdent] -> (PEnv,TCEnv,ValueEnv) -> Interface
>                     -> (PEnv,TCEnv,ValueEnv)
> importInterfaceIntf ms (pEnv,tcEnv,tyEnv) (Interface m is ds) =
>   (importEntitiesIntf precs ds' pEnv,
>    importEntitiesIntf types ds' tcEnv,
>    importEntitiesIntf values ds' tyEnv)
>   where ms' = m : [m | IImportDecl _ m <- is, m `notElem` ms]
>         ds' = map unhide (filter (importEntity . entity) ds)
>         importEntity = maybe True (`elem` ms') . fst . splitQualIdent

> importEntitiesIntf :: Entity a => (IDecl -> [a]) -> [IDecl]
>                    -> TopEnv a -> TopEnv a
> importEntitiesIntf ents ds env = foldr importEntity env (concatMap ents ds)
>   where importEntity x = qualImportTopEnv (origName x) x

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> precs :: IDecl -> [PrecInfo]
> precs (IInfixDecl _ fix p op) = [PrecInfo op (OpPrec fix p)]
> precs _ = []

> types :: IDecl -> [TypeInfo]
> types (IDataDecl _ tc tvs cs _) = [typeCon DataType tc tvs (map constr cs)]
> types (INewtypeDecl _ tc tvs nc _) =
>   [typeCon RenamingType tc tvs (nconstr nc)]
> types (ITypeDecl _ tc tvs ty) = [typeCon AliasType tc tvs (toType tvs ty)]
> types _ = []

> typeCon :: (QualIdent -> Int -> a) -> QualIdent -> [Ident] -> a
> typeCon f tc tvs = f tc (length tvs)

> values :: IDecl -> [ValueInfo]
> values (IDataDecl _ tc tvs cs xs) =
>   map (dataConstr tc tvs ty0) (filter ((`notElem` xs) . constr) cs) ++
>   map (uncurry (fieldLabel tc tvs ty0)) (nubBy sameLabel ls)
>   where ty0 = constrType tc tvs
>         ls = [(l,ty) | RecordDecl _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls, l `notElem` xs]
>         sameLabel (l1,_) (l2,_) = l1 == l2
> values (INewtypeDecl _ tc tvs nc xs) =
>   map (newConstr tc tvs ty0) [nc | nconstr nc `notElem` xs] ++
>   case nc of
>     NewConstrDecl _ _ _ -> []
>     NewRecordDecl _ c l ty -> [fieldLabel tc tvs ty0 l ty | l `notElem` xs]
>   where ty0 = constrType tc tvs
> values (IFunctionDecl _ f n ty) = [Value f n' (polyType ty')]
>   where n' = maybe (arrowArity ty') fromInteger n
>         ty' = toType [] ty
> values _ = []

> dataConstr :: QualIdent -> [Ident] -> TypeExpr -> ConstrDecl -> ValueInfo
> dataConstr tc tvs ty0 (ConstrDecl _ _ c tys) =
>   con tc tvs c (zip (repeat anonId) tys) ty0
> dataConstr tc tvs ty0 (ConOpDecl _ _ ty1 op ty2) =
>   con tc tvs op [(anonId,ty1),(anonId,ty2)] ty0
> dataConstr tc tvs ty0 (RecordDecl _ _ c fs) =
>   con tc tvs c [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls] ty0

> con :: QualIdent -> [Ident] -> Ident -> [(Ident,TypeExpr)] -> TypeExpr
>     -> ValueInfo
> con tc tvs c tys ty0 = DataConstructor (qualifyLike tc c) ls ty
>   where ty = polyType (toType tvs (foldr ArrowType ty0 tys'))
>         (ls,tys') = unzip tys

> newConstr :: QualIdent -> [Ident] -> TypeExpr -> NewConstrDecl -> ValueInfo
> newConstr tc tvs ty0 (NewConstrDecl _ c ty1) = ncon tc tvs c anonId ty1 ty0
> newConstr tc tvs ty0 (NewRecordDecl _ c l ty1) = ncon tc tvs c l ty1 ty0

> ncon :: QualIdent -> [Ident] -> Ident -> Ident -> TypeExpr -> TypeExpr
>      -> ValueInfo
> ncon tc tvs c l ty1 ty0 = NewtypeConstructor (qualifyLike tc c) l ty
>   where ty = polyType (toType tvs (ArrowType ty1 ty0))

> fieldLabel :: QualIdent -> [Ident] -> TypeExpr -> Ident -> TypeExpr
>            -> ValueInfo
> fieldLabel tc tvs ty0 l ty =
>   Value (qualifyLike tc l) 1 (polyType (toType tvs (ArrowType ty0 ty)))

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors. Ditto
for all references to a field label.
\begin{verbatim}

> importUnifyData :: Entity a => TopEnv a -> TopEnv a
> importUnifyData tcEnv =
>   fmap (updWith (foldr (mergeData . snd) zeroFM (allImports tcEnv))) tcEnv
>   where updWith tcs t = fromMaybe t (lookupFM (origName t) tcs)
>         mergeData t tcs =
>           addToFM tc (maybe t (fromJust . merge t) (lookupFM tc tcs)) tcs
>           where tc = origName t

\end{verbatim}
Auxiliary functions:
\begin{verbatim}

> addType :: Import -> Set Ident -> Set Ident
> addType (Import _) tcs = tcs
> addType (ImportTypeWith tc _) tcs = addToSet tc tcs
> addType (ImportTypeAll _) _ = internalError "addType"

> addValue :: Import -> Set Ident -> Set Ident
> addValue (Import f) fs = addToSet f fs
> addValue (ImportTypeWith _ cs) fs = foldr addToSet fs cs
> addValue (ImportTypeAll _) _ = internalError "addValue"

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs = ConstructorType tc (map VariableType tvs)

\end{verbatim}
