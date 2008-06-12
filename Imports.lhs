% -*- LaTeX -*-
% $Id: Imports.lhs 2719 2008-06-12 15:15:07Z wlux $
%
% Copyright (c) 2000-2008, Wolfgang Lux
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
> import Maybe
> import Map
> import PrecInfo
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

> type I a = (Ident,a)

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

> importEntities :: Entity a
>                => (IDecl -> [I a] -> [I a])
>                -> ModuleIdent -> Bool -> (Ident -> Bool) -> (a -> a)
>                -> [IDecl] -> TopEnv a -> TopEnv a
> importEntities bind m q isVisible f ds env =
>   foldr (uncurry (importTopEnv q m)) env
>         [(x,f y) | (x,y) <- foldr bind [] ds, isVisible x]

> importData :: (Ident -> Bool) -> TypeKind -> TypeKind
> importData isVisible (Data tc xs) = Data tc (filter isVisible xs)
> importData _ (Alias tc) = Alias tc

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because all entities are imported into the environments. In addition,
only a qualified import is necessary. Only those entities that are
actually defined in the module are imported. Since the compiler
imports all used interfaces into other interfaces, entities defined in
one module and reexported by another module are made available by
their defining modules. Furthermore, ignoring reexported entities
avoids a problem with the fact that the unqualified name of an entity
defined in an interface may be ambiguous if hidden data type
declarations are taken into account. For instance, for the interface
\begin{verbatim}
  module M where {
    import N;
    hiding data N.T;
    type T a = (a,N.T)
  }
\end{verbatim}
the unqualified type identifier \verb|T| would be ambiguous if
\verb|N.T| were not ignored.
\begin{verbatim}

> importInterfaceIntf :: (PEnv,TCEnv,ValueEnv) -> Interface
>                     -> (PEnv,TCEnv,ValueEnv)
> importInterfaceIntf (pEnv,tcEnv,tyEnv) (Interface m _ ds) =
>   (importEntitiesIntf precs m ds' pEnv,
>    importEntitiesIntf types m ds' tcEnv,
>    importEntitiesIntf values m ds' tyEnv)
>   where ds' = map unhide (filter (isJust . localIdent m . entity) ds)

> unhide :: IDecl -> IDecl
> unhide (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> unhide (HidingDataDecl p tc tvs) = IDataDecl p tc tvs [] []
> unhide (IDataDecl p tc tvs cs _) = IDataDecl p tc tvs cs []
> unhide (INewtypeDecl p tc tvs nc _) = INewtypeDecl p tc tvs nc []
> unhide (ITypeDecl p tc tvs ty) = ITypeDecl p tc tvs ty
> unhide (IFunctionDecl p f n ty) = IFunctionDecl p f n ty

> importEntitiesIntf :: Entity a
>                    => (IDecl -> [I a] -> [I a])
>                    -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntitiesIntf bind m ds env =
>   foldr (uncurry (qualImportTopEnv m)) env (foldr bind [] ds)

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> tidents :: IDecl -> [I TypeKind] -> [I TypeKind]
> tidents (IDataDecl _ tc _ cs xs') =
>   qual tc (Data tc (filter (`notElem` xs') xs))
>   where xs = map constr cs ++ nub (concatMap labels cs)
> tidents (INewtypeDecl _ tc _ nc xs') =
>   qual tc (Data tc (filter (`notElem` xs') xs))
>   where xs = nconstr nc : nlabel nc
> tidents (ITypeDecl _ tc _ _) = qual tc (Alias tc)
> tidents _ = id

> vidents :: IDecl -> [I ValueKind] -> [I ValueKind]
> vidents (IDataDecl _ tc _ cs xs) =
>   cidents tc xs (map constr cs) .
>   lidents tc xs [(l,constrs cs l) | l <- nub (concatMap labels cs)]
>   where constrs cs l = [constr c | c <- cs, l `elem` labels c]
> vidents (INewtypeDecl _ tc _ nc xs) =
>   cidents tc xs [nconstr nc] .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l _ -> lidents tc xs [(l,[c])]
> vidents (IFunctionDecl _ f _ _) = qual f (Var f [])
> vidents _ = id

> precs :: IDecl -> [I PrecInfo] -> [I PrecInfo]
> precs (IInfixDecl _ fix p op) = qual op (PrecInfo op (OpPrec fix p))
> precs _ = id

> types :: IDecl -> [I TypeInfo] -> [I TypeInfo]
> types (IDataDecl _ tc tvs cs _) =
>   qual tc (typeCon DataType tc tvs (map constr cs))
> types (INewtypeDecl _ tc tvs nc _) =
>   qual tc (typeCon RenamingType tc tvs (nconstr nc))
> types (ITypeDecl _ tc tvs ty) =
>   qual tc (typeCon AliasType tc tvs (toType tvs ty))
> types _ = id

> values :: IDecl -> [I ValueInfo] -> [I ValueInfo]
> values (IDataDecl _ tc tvs cs xs) =
>   (map (dataConstr tc tvs ty0) (filter ((`notElem` xs) . constr) cs) ++) .
>   (map (uncurry (fieldLabel tc tvs ty0)) (nubBy sameLabel ls) ++)
>   where ty0 = constrType tc tvs
>         ls = [(l,ty) | RecordDecl _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls, l `notElem` xs]
>         sameLabel (l1,_) (l2,_) = l1 == l2
> values (INewtypeDecl _ tc tvs nc xs) =
>   (map (newConstr tc tvs ty0) [nc | nconstr nc `notElem` xs] ++) .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l ty
>       | l `notElem` xs -> (fieldLabel tc tvs ty0 l ty :)
>       | otherwise -> id
>   where ty0 = constrType tc tvs
> values (IFunctionDecl _ f n ty) = qual f (Value f n' (polyType ty'))
>   where n' = maybe (arrowArity ty') fromInteger n
>         ty' = toType [] ty
> values _ = id

> dataConstr :: QualIdent -> [Ident] -> TypeExpr -> ConstrDecl -> I ValueInfo
> dataConstr tc tvs ty0 (ConstrDecl _ _ c tys) =
>   con tc tvs c (zip (repeat anonId) tys) ty0
> dataConstr tc tvs ty0 (ConOpDecl _ _ ty1 op ty2) =
>   con tc tvs op [(anonId,ty1),(anonId,ty2)] ty0
> dataConstr tc tvs ty0 (RecordDecl _ _ c fs) =
>   con tc tvs c [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls] ty0

> newConstr :: QualIdent -> [Ident] -> TypeExpr -> NewConstrDecl -> I ValueInfo
> newConstr tc tvs ty0 (NewConstrDecl _ c ty1) = ncon tc tvs c anonId ty1 ty0
> newConstr tc tvs ty0 (NewRecordDecl _ c l ty1) = ncon tc tvs c l ty1 ty0

> fieldLabel :: QualIdent -> [Ident] -> TypeExpr -> Ident -> TypeExpr
>            -> I ValueInfo
> fieldLabel tc tvs ty0 l ty =
>   (l,Value (qualifyLike tc l) 1 (polyType (toType tvs (ArrowType ty0 ty))))

> qual :: QualIdent -> a -> [I a] -> [I a]
> qual x y = ((unqualify x,y) :)

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

> cidents :: QualIdent -> [Ident] -> [Ident] -> [I ValueKind] -> [I ValueKind]
> cidents tc xs cs = (map (cident tc) (filter (`notElem` xs) cs) ++)

> cident :: QualIdent -> Ident -> I ValueKind
> cident tc c = (c,Constr (qualifyLike tc c))

> lidents :: QualIdent -> [Ident] -> [(Ident,[Ident])] -> [I ValueKind]
>         -> [I ValueKind]
> lidents tc xs ls = (map (uncurry (lident tc)) ls' ++)
>   where ls' = filter ((`notElem` xs) . fst) ls

> lident :: QualIdent -> Ident -> [Ident] -> I ValueKind
> lident tc l cs = (l,Var (qualifyLike tc l) (map (qualifyLike tc) cs))

> typeCon :: (QualIdent -> Int -> a) -> QualIdent -> [Ident] -> a
> typeCon f tc tvs = f tc (length tvs)

> con :: QualIdent -> [Ident] -> Ident -> [(Ident,TypeExpr)] -> TypeExpr
>     -> I ValueInfo
> con tc tvs c tys ty0 = (c,DataConstructor (qualifyLike tc c) ls ty)
>   where ty = polyType (toType tvs (foldr ArrowType ty0 tys'))
>         (ls,tys') = unzip tys

> ncon :: QualIdent -> [Ident] -> Ident -> Ident -> TypeExpr -> TypeExpr
>      -> I ValueInfo
> ncon tc tvs c l ty1 ty0 = (c,NewtypeConstructor (qualifyLike tc c) l ty)
>   where ty = polyType (toType tvs (ArrowType ty1 ty0))

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs = ConstructorType tc (map VariableType tvs)

\end{verbatim}
