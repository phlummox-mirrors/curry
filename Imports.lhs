% -*- LaTeX -*-
% $Id: Imports.lhs 1770 2005-09-21 11:04:37Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Imports.lhs}
\section{Importing Interfaces}
This module provides a few functions which can be used to import
interfaces into the current module.
\begin{verbatim}

> module Imports(importInterface,importInterfaceIntf,importUnifyData) where
> import Base
> import Env
> import TopEnv
> import Maybe
> import Map
> import Set

\end{verbatim}
Three kinds of environments are computed from the interface, one
containing the operator precedences, another for the type
constructors, and the third containing the types of the data
constructors and functions. In addition, two intermediate environments
containing only type and value identifier information are used for
checking the optional import or hiding list of an import declaration.
Note that the original names of all entities defined in the imported
module are qualified appropriately. The same is true for type
expressions.
\begin{verbatim}

> type ExpTypeEnv = Env Ident TypeKind
> type ExpFunEnv = Env Ident ValueKind

> type ExpPEnv = Env Ident PrecInfo
> type ExpTCEnv = Env Ident TypeInfo
> type ExpValueEnv = Env Ident ValueInfo

\end{verbatim}
When an interface is imported, the compiler first transforms the
interface into these environments. If an import specification is
present, the environments are restricted to only those entities which
are included in the specification or not hidden by it, respectively.
The resulting environments are then imported into the current module
using either a qualified import or both a qualified and an unqualified
import.
\begin{verbatim}

> importInterface :: Position -> ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,ValueEnv)
> importInterface p m q is (pEnv,tcEnv,tyEnv) i =
>   (importEntities m q vs id (intfEnv bindPrec i) pEnv,
>    importEntities m q ts (importData vs) mTCEnv tcEnv,
>    importEntities m q vs id mTyEnv tyEnv)
>   where mTCEnv = intfEnv bindTC i
>         mTyEnv = intfEnv bindType i
>         is' = checkImports mTCEnv mTyEnv i is
>         ts = isVisible addType is'
>         vs = isVisible addValue is'

> checkImports :: ExpTCEnv -> ExpValueEnv -> Interface
>              -> Maybe ImportSpec -> Maybe ImportSpec
> checkImports tcEnv tyEnv (Interface m _ _) = fmap (expandSpecs m tEnv vEnv)
>   where tEnv = fmap typeKind tcEnv
>         vEnv = fmap valueKind tyEnv

> isVisible :: (Import -> Set Ident -> Set Ident) -> Maybe ImportSpec
>           -> Ident -> Bool
> isVisible add (Just (Importing _ xs)) = (`elemSet` foldr add zeroSet xs)
> isVisible add (Just (Hiding _ xs)) = (`notElemSet` foldr add zeroSet xs)
> isVisible _ Nothing = const True

> importEntities :: Entity a => ModuleIdent -> Bool -> (Ident -> Bool)
>                -> (a -> a) -> Env Ident a -> TopEnv a -> TopEnv a
> importEntities m q isVisible f mEnv env =
>   foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
>         [(x,f y) | (x,y) <- envToList mEnv, isVisible x]
>   where importUnqual m x y = importTopEnv m x y . qualImportTopEnv m x y

> importData :: (Ident -> Bool) -> TypeInfo -> TypeInfo
> importData isVisible (DataType tc n cs) =
>   DataType tc n (map (>>= importConstr isVisible) cs)
> importData isVisible (RenamingType tc n nc) =
>   maybe (DataType tc n []) (RenamingType tc n) (importConstr isVisible nc)
> importData isVisible (AliasType tc n ty) = AliasType tc n ty

> importConstr :: (Ident -> Bool) -> Ident -> Maybe Ident
> importConstr isVisible c
>   | isVisible c = Just c
>   | otherwise = Nothing

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because all entities are imported into the environment. In addition,
only a qualified import is necessary. Note that hidden data types are
imported as well because they may be used in type expressions in an
interface.
\begin{verbatim}

> importInterfaceIntf :: (PEnv,TCEnv,ValueEnv) -> Interface
>                     -> (PEnv,TCEnv,ValueEnv)
> importInterfaceIntf (pEnv,tcEnv,tyEnv) i@(Interface m _ _) =
>   (importEntitiesIntf m (intfEnv bindPrec i) pEnv,
>    importEntitiesIntf m (intfEnv bindTCHidden i) tcEnv,
>    importEntitiesIntf m (intfEnv bindType i) tyEnv)

> importEntitiesIntf :: Entity a => ModuleIdent -> Env Ident a
>                    -> TopEnv a -> TopEnv a
> importEntitiesIntf m mEnv env =
>   foldr (uncurry (qualImportTopEnv m)) env (envToList mEnv)

\end{verbatim}
In a first step, the three export environments are initialized from
the interface's declarations. This step also qualifies the names of
all entities defined in (but not imported into) the interface with its
module name.
\begin{verbatim}

> intfEnv :: (ModuleIdent -> IDecl -> Env Ident a -> Env Ident a)
>         -> Interface -> Env Ident a
> intfEnv bind (Interface m _ ds) = foldr (bind m) emptyEnv ds

> bindPrec :: ModuleIdent -> IDecl -> ExpPEnv -> ExpPEnv
> bindPrec m (IInfixDecl _ fix p op) =
>   bindUnqual op (PrecInfo (qualQualify m op) (OpPrec fix p))
> bindPrec _ _ = id

> bindTC :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
> bindTC m (IDataDecl _ tc tvs cs) =
>   bindUnqual tc (typeCon DataType m tc tvs (map (fmap constr) cs))
> bindTC m (INewtypeDecl _ tc tvs nc) =
>   bindUnqual tc (typeCon RenamingType m tc tvs (nconstr nc))
> bindTC m (ITypeDecl _ tc tvs ty) =
>   bindUnqual tc (typeCon AliasType m tc tvs (toQualType m tvs ty))
> bindTC _ _ = id

> bindTCHidden :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
> bindTCHidden m (HidingDataDecl _ tc tvs) =
>   bindEnv tc (typeCon DataType m (qualify tc) tvs [])
> bindTCHidden m d = bindTC m d

> bindType :: ModuleIdent -> IDecl -> ExpValueEnv -> ExpValueEnv
> bindType m (IDataDecl _ tc tvs cs) =
>   flip (foldr (bindConstr m tc' tvs (constrType tc' tvs))) (catMaybes cs)
>   where tc' = qualQualify m tc
> bindType m (INewtypeDecl _ tc tvs nc) =
>   bindNewConstr m tc' tvs (constrType tc' tvs) nc
>   where tc' = qualQualify m tc
> bindType m (IFunctionDecl _ f ty) =
>   bindUnqual f (Value (qualQualify m f) (polyType (toQualType m [] ty)))
> bindType _ _ = id

> bindConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl
>            -> ExpValueEnv -> ExpValueEnv
> bindConstr m tc tvs ty0 (ConstrDecl _ evs c tys) =
>   bindEnv c (con DataConstructor m tc tvs evs c (foldr ArrowType ty0 tys))
> bindConstr m tc tvs ty0 (ConOpDecl _ evs ty1 op ty2) =
>   bindEnv op
>     (con DataConstructor m tc tvs evs op (ArrowType ty1 (ArrowType ty2 ty0)))

> bindNewConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr
>               -> NewConstrDecl -> ExpValueEnv -> ExpValueEnv
> bindNewConstr m tc tvs ty0 (NewConstrDecl _ evs c ty1) =
>   bindEnv c (con NewtypeConstructor m tc tvs evs c (ArrowType ty1 ty0))

> bindUnqual :: QualIdent -> a -> Env Ident a -> Env Ident a
> bindUnqual x = bindEnv (unqualify x)

\end{verbatim}
After the environments have been initialized, the optional import
specifications can be checked. There are two kinds of import
specifications, a ``normal'' one, which names the entities that shall
be imported, and a hiding specification, which lists those entities
that shall not be imported.

There is a subtle difference between both kinds of
specifications. While it is not allowed to list a data constructor
outside of its type in a ``normal'' specification, it is allowed to
hide a data constructor explicitly. E.g., if module \texttt{A} exports
the data type \texttt{T} with constructor \texttt{C}, the data
constructor can be imported with one of the two specifications
\begin{verbatim}
import A(T(C))
import A(T(..))
\end{verbatim}
but can be hidden in three different ways:
\begin{verbatim}
import A hiding(C)
import A hiding(T(C))
import A hiding(T(..))
\end{verbatim}

The functions \texttt{expandImport} and \texttt{expandHiding} check
that all entities in an import specification are actually exported
from the module. In addition, all imports of type constructors are
changed into a \texttt{T()} specification and explicit imports for the
data constructors are added.
\begin{verbatim}

> expandSpecs :: ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> ImportSpec
>             -> ImportSpec
> expandSpecs m tEnv vEnv (Importing p is) =
>   Importing p (concat (map (expandImport p m tEnv vEnv) is))
> expandSpecs m tEnv vEnv (Hiding p is) =
>   Hiding p (concat (map (expandHiding p m tEnv vEnv) is))

> expandImport :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Import
>              -> [Import]
> expandImport p m tEnv vEnv (Import x) = expandThing p m tEnv vEnv x
> expandImport p m tEnv vEnv (ImportTypeWith tc cs) =
>   [expandTypeWith p m tEnv tc cs]
> expandImport p m tEnv vEnv (ImportTypeAll tc) =
>   [expandTypeAll p m tEnv tc]

> expandHiding :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Import
>              -> [Import]
> expandHiding p m tEnv vEnv (Import x) = expandHide p m tEnv vEnv x
> expandHiding p m tEnv vEnv (ImportTypeWith tc cs) =
>   [expandTypeWith p m tEnv tc cs]
> expandHiding p m tEnv vEnv (ImportTypeAll tc) =
>   [expandTypeAll p m tEnv tc]

> expandThing :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Ident
>             -> [Import]
> expandThing p m tEnv vEnv tc =
>   case lookupEnv tc tEnv of
>     Just _ -> expandThing' p m vEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandThing' p m vEnv tc Nothing

> expandThing' :: Position -> ModuleIdent -> ExpFunEnv -> Ident
>              -> Maybe [Import] -> [Import]
> expandThing' p m vEnv f tcImport =
>   case lookupEnv f vEnv of
>     Just (Constr _ _) -> maybe (errorAt p (importDataConstr m f)) id tcImport
>     Just (Var _) -> Import f : maybe [] id tcImport
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) id tcImport

> expandHide :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Ident
>            -> [Import]
> expandHide p m tEnv vEnv tc =
>   case lookupEnv tc tEnv of
>     Just _ -> expandHide' p m vEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandHide' p m vEnv tc Nothing

> expandHide' :: Position -> ModuleIdent -> ExpFunEnv -> Ident
>             -> Maybe [Import] -> [Import]
> expandHide' p m vEnv f tcImport =
>   case lookupEnv f vEnv of
>     Just _ -> Import f : maybe [] id tcImport
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) id tcImport

> expandTypeWith :: Position -> ModuleIdent -> ExpTypeEnv -> Ident -> [Ident]
>                -> Import
> expandTypeWith p m tEnv tc cs =
>   case lookupEnv tc tEnv of
>     Just (Data _ _ cs') -> ImportTypeWith tc (map (checkConstr cs') cs)
>     Just (Alias _ _) -> errorAt p (nonDataType m tc)
>     Nothing -> errorAt p (undefinedType m tc)
>   where checkConstr cs c
>           | c `elem` cs = c
>           | otherwise = errorAt p (undefinedDataConstr m tc c)

> expandTypeAll :: Position -> ModuleIdent -> ExpTypeEnv -> Ident -> Import
> expandTypeAll p m tEnv tc =
>   case lookupEnv tc tEnv of
>     Just (Data _ _ cs) -> ImportTypeWith tc cs
>     Just (Alias _ _) -> errorAt p (nonDataType m tc)
>     Nothing -> errorAt p (undefinedType m tc)

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors.
\begin{verbatim}

> importUnifyData :: TCEnv -> TCEnv
> importUnifyData tcEnv =
>   fmap (setInfo (foldr (mergeData . snd) zeroFM (allImports tcEnv))) tcEnv
>   where setInfo tcs t = fromJust (lookupFM (origName t) tcs)
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

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> QualIdent -> [Ident] -> a
> typeCon f m tc tvs = f (qualQualify m tc) (length tvs)

> con :: (QualIdent -> ExistTypeScheme -> a) -> ModuleIdent -> QualIdent
>     -> [Ident] -> [Ident] -> Ident -> TypeExpr -> a
> con f m tc tvs evs c ty =
>   f (qualifyLike tc c)
>     (ForAllExist (length tvs) (length evs) (toQualType m tvs ty))

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs = ConstructorType tc (map VariableType tvs)

\end{verbatim}
Error messages:
\begin{verbatim}

> undefinedEntity :: ModuleIdent -> Ident -> String
> undefinedEntity m x = name x ++ " is not defined in module " ++ moduleName m

> undefinedType :: ModuleIdent -> Ident -> String
> undefinedType m tc =
>   "Type " ++ name tc ++ " is not defined in module " ++ moduleName m

> undefinedDataConstr :: ModuleIdent -> Ident -> Ident -> String
> undefinedDataConstr m tc c =
>   name c ++ " is not a data constructor of type " ++ name tc

> nonDataType :: ModuleIdent -> Ident -> String
> nonDataType m tc = name tc ++ " is not a data type"

> importDataConstr :: ModuleIdent -> Ident -> String
> importDataConstr m c = "Explicit import for data constructor " ++ name c

\end{verbatim}
