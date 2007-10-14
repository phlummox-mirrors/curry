% -*- LaTeX -*-
% $Id: Imports.lhs 2498 2007-10-14 13:16:00Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
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
> importIdents m q is (tEnv,vEnv) (Interface m' _ ds) =
>   (importEntities tidents m q ts (importData vs) m' ds tEnv,
>    importEntities vidents m q vs id m' ds vEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,ValueEnv)
> importInterface m q is (pEnv,tcEnv,tyEnv) (Interface m' _ ds) =
>   (importEntities precs m q vs id m' ds pEnv,
>    importEntities types m q ts id m' ds tcEnv,
>    importEntities values m q vs id m' ds tyEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> isVisible :: (Import -> Set Ident -> Set Ident) -> Maybe ImportSpec
>           -> Ident -> Bool
> isVisible add (Just (Importing _ xs)) = (`elemSet` foldr add zeroSet xs)
> isVisible add (Just (Hiding _ xs)) = (`notElemSet` foldr add zeroSet xs)
> isVisible _ Nothing = const True

> importEntities :: Entity a
>                => (ModuleIdent -> IDecl -> [I a] -> [I a])
>                -> ModuleIdent -> Bool -> (Ident -> Bool) -> (a -> a)
>                -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntities bind m q isVisible f m' ds env =
>   foldr (uncurry (importTopEnv q m)) env
>         [(x,f y) | (x,y) <- foldr (bind m') [] ds, isVisible x]

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
avoids a problem with the fact that the unqualified names of entities
defined in an interface may be ambiguous if hidden data type
declarations are taken into account. For instance, in the interface
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

> entity :: IDecl -> QualIdent
> entity (IInfixDecl _ _ _ op) = op
> entity (HidingDataDecl _ tc _) = tc
> entity (IDataDecl _ tc _ _ _) = tc
> entity (INewtypeDecl _ tc _ _ _) = tc
> entity (ITypeDecl _ tc _ _) = tc
> entity (IFunctionDecl _ f _ _) = f

> unhide :: IDecl -> IDecl
> unhide (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> unhide (HidingDataDecl p tc tvs) = IDataDecl p tc tvs [] []
> unhide (IDataDecl p tc tvs cs _) = IDataDecl p tc tvs cs []
> unhide (INewtypeDecl p tc tvs nc _) = INewtypeDecl p tc tvs nc []
> unhide (ITypeDecl p tc tvs ty) = ITypeDecl p tc tvs ty
> unhide (IFunctionDecl p f n ty) = IFunctionDecl p f n ty

> importEntitiesIntf :: Entity a
>                    => (ModuleIdent -> IDecl -> [I a] -> [I a])
>                    -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntitiesIntf bind m ds env =
>   foldr (uncurry (qualImportTopEnv m)) env (foldr (bind m) [] ds)

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> tidents :: ModuleIdent -> IDecl -> [I TypeKind] -> [I TypeKind]
> tidents m (IDataDecl _ tc _ cs xs') =
>   qual tc (tident Data m tc (filter (`notElem` xs') xs))
>   where xs = map constr cs ++ nub (concatMap labels cs)
> tidents m (INewtypeDecl _ tc _ nc xs') =
>   qual tc (tident Data m tc (filter (`notElem` xs') xs))
>   where xs = nconstr nc : nlabel nc
> tidents m (ITypeDecl _ tc _ _) = qual tc (tident Alias m tc)
> tidents _ _ = id

> vidents :: ModuleIdent -> IDecl -> [I ValueKind] -> [I ValueKind]
> vidents m (IDataDecl _ tc _ cs xs) =
>   cidents m tc xs (map constr cs) .
>   lidents m tc xs [(l,constrs cs l) | l <- nub (concatMap labels cs)]
>   where constrs cs l = [constr c | c <- cs, l `elem` labels c]
> vidents m (INewtypeDecl _ tc _ nc xs) =
>   cidents m tc xs [nconstr nc] .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l _ -> lidents m tc xs [(l,[c])]
> vidents m (IFunctionDecl _ f _ _) = qual f (Var (qualQualify m f) [])
> vidents _ _ = id

> precs :: ModuleIdent -> IDecl -> [I PrecInfo] -> [I PrecInfo]
> precs m (IInfixDecl _ fix p op) =
>   qual op (PrecInfo (qualQualify m op) (OpPrec fix p))
> precs _ _ = id

> types :: ModuleIdent -> IDecl -> [I TypeInfo] -> [I TypeInfo]
> types m (IDataDecl _ tc tvs cs _) =
>   qual tc (typeCon DataType m tc tvs (map constr cs))
> types m (INewtypeDecl _ tc tvs nc _) =
>   qual tc (typeCon RenamingType m tc tvs (nconstr nc))
> types m (ITypeDecl _ tc tvs ty) =
>   qual tc (typeCon AliasType m tc tvs (toType m tvs ty))
> types _ _ = id

> values :: ModuleIdent -> IDecl -> [I ValueInfo] -> [I ValueInfo]
> values m (IDataDecl _ tc tvs cs xs) =
>   (map (dataConstr m tc' tvs ty0) (filter ((`notElem` xs) . constr) cs) ++) .
>   (map (uncurry (fieldLabel m tc' tvs ty0)) (nubBy sameLabel ls) ++)
>   where tc' = qualQualify m tc
>         ty0 = constrType tc' tvs
>         ls = [(l,ty) | RecordDecl _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls, l `notElem` xs]
>         sameLabel (l1,_) (l2,_) = l1 == l2
> values m (INewtypeDecl _ tc tvs nc xs) =
>   (map (newConstr m tc' tvs ty0) [nc | nconstr nc `notElem` xs] ++) .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l ty
>       | l `notElem` xs -> (fieldLabel m tc' tvs ty0 l ty :)
>       | otherwise -> id
>   where tc' = qualQualify m tc
>         ty0 = constrType tc' tvs
> values m (IFunctionDecl _ f n ty) =
>   qual f (Value (qualQualify m f) n' (polyType ty'))
>   where n' = maybe (arrowArity ty') fromInteger n
>         ty' = toType m [] ty
> values _ _ = id

> dataConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl
>            -> I ValueInfo
> dataConstr m tc tvs ty0 (ConstrDecl _ _ c tys) =
>   (c,con m tc tvs c (zip (repeat anonId) tys) ty0)
> dataConstr m tc tvs ty0 (ConOpDecl _ _ ty1 op ty2) =
>   (op,con m tc tvs op [(anonId,ty1),(anonId,ty2)] ty0)
> dataConstr m tc tvs ty0 (RecordDecl _ _ c fs) =
>   (c,con m tc tvs c [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls] ty0)

> newConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> NewConstrDecl
>           -> I ValueInfo
> newConstr m tc tvs ty0 (NewConstrDecl _ c ty1) =
>   (c,ncon m tc tvs c anonId ty1 ty0)
> newConstr m tc tvs ty0 (NewRecordDecl _ c l ty1) =
>   (c,ncon m tc tvs c l ty1 ty0)

> fieldLabel :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> Ident
>            -> TypeExpr -> I ValueInfo
> fieldLabel m tc tvs ty0 l ty =
>   (l,Value (qualifyLike tc l) 1 (polyType (toType m tvs (ArrowType ty0 ty))))

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

> tident :: (QualIdent -> a) -> ModuleIdent -> QualIdent -> a
> tident f m tc = f (qualQualify m tc)

> cidents :: ModuleIdent -> QualIdent -> [Ident] -> [Ident] -> [I ValueKind]
>         -> [I ValueKind]
> cidents m tc xs cs =
>   (map (cident (qualQualify m tc)) (filter (`notElem` xs) cs) ++)

> cident :: QualIdent -> Ident -> I ValueKind
> cident tc c = (c,Constr (qualifyLike tc c))

> lidents :: ModuleIdent -> QualIdent -> [Ident] -> [(Ident,[Ident])]
>         -> [I ValueKind] -> [I ValueKind]
> lidents m tc xs ls = (map (uncurry (lident (qualQualify m tc))) ls' ++)
>   where ls' = filter ((`notElem` xs) . fst) ls

> lident :: QualIdent -> Ident -> [Ident] -> I ValueKind
> lident tc l cs = (l,Var (qualifyLike tc l) (map (qualifyLike tc) cs))

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> QualIdent -> [Ident] -> a
> typeCon f m tc tvs = f (qualQualify m tc) (length tvs)

> con :: ModuleIdent -> QualIdent -> [Ident] -> Ident -> [(Ident,TypeExpr)]
>     -> TypeExpr -> ValueInfo
> con m tc tvs c tys ty0 = DataConstructor (qualifyLike tc c) (length tys) ls ty
>   where ty = polyType (toType m tvs (foldr ArrowType ty0 tys'))
>         (ls,tys') = unzip tys

> ncon :: ModuleIdent -> QualIdent -> [Ident] -> Ident -> Ident -> TypeExpr
>      -> TypeExpr -> ValueInfo
> ncon m tc tvs c l ty1 ty0 = NewtypeConstructor (qualifyLike tc c) l ty
>   where ty = polyType (toType m tvs (ArrowType ty1 ty0))

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs = ConstructorType tc (map VariableType tvs)

\end{verbatim}
