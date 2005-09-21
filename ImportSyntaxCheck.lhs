% -*- LaTeX -*-
% $Id: ImportSyntaxCheck.lhs 1771 2005-09-21 14:18:10Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ImportSyntaxCheck.lhs}
\section{Checking Import Lists}
Before actually importing definitions into the current module, the
compiler first checks and expands the import specifications of all
import declarations.
\begin{verbatim}

> module ImportSyntaxCheck(checkImports) where
> import Base
> import Env
> import Maybe

> checkImports :: Interface -> Maybe ImportSpec -> Maybe ImportSpec
> checkImports (Interface m _ ds) = fmap (expandSpecs m tEnv vEnv)
>   where tEnv = foldr (bindType m) emptyEnv ds
>         vEnv = foldr (bindValue m) emptyEnv ds

\end{verbatim}
The compiler uses two environments collecting the type and value
identifiers, respectively, declared in the interface. In a first step,
the two export environments are initialized from the interface's
declarations.
\begin{verbatim}

> type ExpTypeEnv = Env Ident TypeKind
> type ExpFunEnv = Env Ident ValueKind

> bindType :: ModuleIdent -> IDecl -> ExpTypeEnv -> ExpTypeEnv
> bindType m (IDataDecl _ tc tvs cs) =
>   bindUnqual tc (typeCon Data m tc tvs (map constr (catMaybes cs)))
> bindType m (INewtypeDecl _ tc tvs nc) =
>   bindUnqual tc (typeCon Data m tc tvs [nconstr nc])
> bindType m (ITypeDecl _ tc tvs _) = bindUnqual tc (typeCon Alias m tc tvs)
> bindType _ _ = id

> bindValue :: ModuleIdent -> IDecl -> ExpFunEnv -> ExpFunEnv
> bindValue m (IDataDecl _ tc _ cs) =
>   flip (foldr (bindConstr (qualQualify m tc))) (catMaybes cs)
> bindValue m (INewtypeDecl _ tc _ nc) = bindNewConstr (qualQualify m tc) nc
> bindValue m (IFunctionDecl _ f _) = bindUnqual f (Var (qualQualify m f))
> bindValue _ _ = id

> bindConstr :: QualIdent -> ConstrDecl -> ExpFunEnv -> ExpFunEnv
> bindConstr tc (ConstrDecl _ _ c tys) = bindEnv c (con tc c (length tys))
> bindConstr tc (ConOpDecl _ _ _ op _) = bindEnv op (con tc op 2)

> bindNewConstr :: QualIdent -> NewConstrDecl -> ExpFunEnv -> ExpFunEnv
> bindNewConstr tc (NewConstrDecl _ _ c _) = bindEnv c (con tc c 1)

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
>     Just (Constr _ _) -> fromMaybe (errorAt p (importDataConstr m f)) tcImport
>     Just (Var _) -> Import f : fromMaybe [] tcImport
>     Nothing -> fromMaybe (errorAt p (undefinedEntity m f)) tcImport

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
>     Just _ -> Import f : fromMaybe [] tcImport
>     Nothing -> fromMaybe (errorAt p (undefinedEntity m f)) tcImport

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
Auxiliary functions:
\begin{verbatim}

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> QualIdent -> [Ident] -> a
> typeCon f m tc tvs = f (qualQualify m tc) (length tvs)

> con :: QualIdent -> Ident -> Int -> ValueKind
> con tc c = Constr (qualifyLike tc c)

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
