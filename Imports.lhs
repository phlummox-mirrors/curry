% -*- LaTeX -*-
% $Id: Imports.lhs 2472 2007-09-19 14:55:02Z wlux $
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
>   (importEntities tidents m q ts (importData vs) m' ds' tEnv,
>    importEntities vidents m q vs id m' ds' vEnv)
>   where ds' = filter (not . isHiddenData) ds
>         ts = isVisible addType is
>         vs = isVisible addValue is

> importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,ValueEnv)
> importInterface m q is (pEnv,tcEnv,tyEnv) (Interface m' _ ds) =
>   (importEntities precs m q vs id m' ds' pEnv,
>    importEntities types m q ts id m' ds' tcEnv,
>    importEntities values m q vs id m' ds' tyEnv)
>   where ds' = filter (not . isHiddenData) ds
>         ts = isVisible addType is
>         vs = isVisible addValue is

> isHiddenData :: IDecl -> Bool
> isHiddenData (IInfixDecl _ _ _ _) = False
> isHiddenData (HidingDataDecl _ _ _) = True 
> isHiddenData (IDataDecl _ _ _ _) = False
> isHiddenData (INewtypeDecl _ _ _ _) = False
> isHiddenData (ITypeDecl _ _ _ _) = False
> isHiddenData (IFunctionDecl _ _ _ _) = False

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
> importData isVisible (Data tc cs) = Data tc (filter isVisible cs)
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
>   where ds' = filter (isJust . localIdent m . entity) ds

> entity :: IDecl -> QualIdent
> entity (IInfixDecl _ _ _ op) = op
> entity (HidingDataDecl _ tc _) = tc
> entity (IDataDecl _ tc _ _) = tc
> entity (INewtypeDecl _ tc _ _) = tc
> entity (ITypeDecl _ tc _ _) = tc
> entity (IFunctionDecl _ f _ _) = f

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
> tidents m (HidingDataDecl _ tc _) = qual tc (tident Data m tc [])
> tidents m (IDataDecl _ tc _ cs) =
>   qual tc (tident Data m tc (map constr (catMaybes cs)))
> tidents m (INewtypeDecl _ tc _ nc) = qual tc (tident Data m tc [nconstr nc])
> tidents m (ITypeDecl _ tc _ _) = qual tc (tident Alias m tc)
> tidents _ _ = id

> vidents :: ModuleIdent -> IDecl -> [I ValueKind] -> [I ValueKind]
> vidents m (IDataDecl _ tc _ cs) =
>   (map (cident (qualQualify m tc) . constr) (catMaybes cs) ++)
> vidents m (INewtypeDecl _ tc _ nc) =
>   (cident (qualQualify m tc) (nconstr nc) :)
> vidents m (IFunctionDecl _ f _ _) = qual f (Var (qualQualify m f))
> vidents _ _ = id

> precs :: ModuleIdent -> IDecl -> [I PrecInfo] -> [I PrecInfo]
> precs m (IInfixDecl _ fix p op) =
>   qual op (PrecInfo (qualQualify m op) (OpPrec fix p))
> precs _ _ = id

> types :: ModuleIdent -> IDecl -> [I TypeInfo] -> [I TypeInfo]
> types m (HidingDataDecl _ tc tvs) = qual tc (typeCon DataType m tc tvs [])
> types m (IDataDecl _ tc tvs cs) =
>   qual tc (typeCon DataType m tc tvs (map (fmap constr) cs))
> types m (INewtypeDecl _ tc tvs nc) =
>   qual tc (typeCon RenamingType m tc tvs (nconstr nc))
> types m (ITypeDecl _ tc tvs ty) =
>   qual tc (typeCon AliasType m tc tvs (toType m tvs ty))
> types _ _ = id

> values :: ModuleIdent -> IDecl -> [I ValueInfo] -> [I ValueInfo]
> values m (IDataDecl _ tc tvs cs) =
>   (map (dataConstr m tc' tvs (constrType tc' tvs)) (catMaybes cs) ++)
>   where tc' = qualQualify m tc
> values m (INewtypeDecl _ tc tvs nc) =
>   (newConstr m tc' tvs (constrType tc' tvs) nc :)
>   where tc' = qualQualify m tc
> values m (IFunctionDecl _ f n ty) =
>   qual f (Value (qualQualify m f) n' (polyType ty'))
>   where n' = maybe (arrowArity ty') fromInteger n
>         ty' = toType m [] ty
> values _ _ = id

> dataConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl
>            -> I ValueInfo
> dataConstr m tc tvs ty0 (ConstrDecl _ _ c tys) =
>   (c,con DataConstructor m tc tvs c (length tys) (foldr ArrowType ty0 tys))
> dataConstr m tc tvs ty0 (ConOpDecl _ _ ty1 op ty2) =
>   (op,con DataConstructor m tc tvs op 2 (ArrowType ty1 (ArrowType ty2 ty0)))

> newConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> NewConstrDecl
>           -> I ValueInfo
> newConstr m tc tvs ty0 (NewConstrDecl _ c ty1) =
>   (c,con (const . NewtypeConstructor) m tc tvs c 1 (ArrowType ty1 ty0))

> qual :: QualIdent -> a -> [I a] -> [I a]
> qual x y = ((unqualify x,y) :)

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors.
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

> cident :: QualIdent -> Ident -> I ValueKind
> cident tc c = (c,Constr (qualifyLike tc c))

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> QualIdent -> [Ident] -> a
> typeCon f m tc tvs = f (qualQualify m tc) (length tvs)

> con :: (QualIdent -> Int -> TypeScheme -> a) -> ModuleIdent -> QualIdent
>     -> [Ident] -> Ident -> Int -> TypeExpr -> a
> con f m tc tvs c n ty = f (qualifyLike tc c) n (polyType (toType m tvs ty))

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs = ConstructorType tc (map VariableType tvs)

\end{verbatim}
