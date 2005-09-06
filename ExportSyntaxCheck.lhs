% -*- LaTeX -*-
% $Id: ExportSyntaxCheck.lhs 1762 2005-09-06 15:02:17Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ExportSyntaxCheck.lhs}
\section{Checking Module Interfaces}
The function \texttt{checkExports} checks the export specifications of
the module and expands them into a list containing all exported types
and functions, combining multiple exports for the same entity. The
expanded export specifications refer to the original names of all
entities.
\begin{verbatim}

> module ExportSyntaxCheck(checkExports) where
> import Base
> import List
> import Map
> import Maybe
> import Set
> import TopEnv

> checkExports :: ModuleIdent -> [ImportDecl] -> TCEnv -> ValueEnv
>              -> Maybe ExportSpec -> ExportSpec
> checkExports m is tcEnv tyEnv es = Exporting noPos $
>   maybe (expandLocalModule tcEnv tyEnv)
>         (checkInterface . nubExports . expandSpecs ms m tcEnv tyEnv)
>         es
>   where ms = fromListSet [fromMaybe m asM | ImportDecl _ m _ asM _ <- is]
>         noPos = undefined

> checkInterface :: [Export] -> [Export]
> checkInterface es =
>   case linear [unqualify tc | ExportTypeWith tc _ <- es] of
>     Linear ->
>       case linear ([c | ExportTypeWith _ cs <- es, c <- cs] ++
>                    [unqualify f | Export f <- es]) of
>         Linear -> es
>         NonLinear v -> error (ambiguousExportValue v)
>     NonLinear tc -> error (ambiguousExportType tc)

\end{verbatim}
While checking all export specifications, the compiler expands
specifications of the form \verb|T(..)| into
\texttt{T($C_1,\dots,C_n$)}, where $C_1,\dots,C_n$ are the data
constructors of type \texttt{T}, and replaces an export specification
\verb|module M| by specifications for all entities which are defined
in module \texttt{M} and imported into the current module with their
unqualified name. In order to distinguish exported type constructors
from exported functions, the former are translated into the equivalent
form \verb|T()|. Note that the export specification \texttt{x} may
export a type constructor \texttt{x} \emph{and} a global function
\texttt{x} at the same time.
\begin{verbatim}

> expandSpecs :: Set ModuleIdent -> ModuleIdent -> TCEnv -> ValueEnv
>             -> ExportSpec -> [Export]
> expandSpecs ms m tcEnv tyEnv (Exporting p es) =
>   concat (map (expandExport p ms m tcEnv tyEnv) es)

> expandExport :: Position -> Set ModuleIdent -> ModuleIdent -> TCEnv
>              -> ValueEnv -> Export -> [Export]
> expandExport p _ _ tcEnv tyEnv (Export x) = expandThing p tcEnv tyEnv x
> expandExport p _ _ tcEnv _ (ExportTypeWith tc cs) =
>   [expandTypeWith p tcEnv tc cs]
> expandExport p _ _ tcEnv _ (ExportTypeAll tc) = [expandTypeAll p tcEnv tc]
> expandExport p ms m tcEnv tyEnv (ExportModule m')
>   | m == m' = (if m `elemSet` ms then expandModule tcEnv tyEnv m else [])
>               ++ expandLocalModule tcEnv tyEnv
>   | m' `elemSet` ms = expandModule tcEnv tyEnv m'
>   | otherwise = errorAt p (moduleNotImported m')

> expandThing :: Position -> TCEnv -> ValueEnv -> QualIdent -> [Export]
> expandThing p tcEnv tyEnv tc =
>   case qualLookupTC tc tcEnv of
>     [] -> expandThing' p tyEnv tc Nothing
>     [t] -> expandThing' p tyEnv tc (Just [ExportTypeWith (origName t) []])
>     _ -> errorAt p (ambiguousType tc)

> expandThing' :: Position -> ValueEnv -> QualIdent -> Maybe [Export]
>              -> [Export]
> expandThing' p tyEnv f tcExport =
>   case qualLookupValue f tyEnv of
>     [] -> fromMaybe (errorAt p (undefinedEntity f)) tcExport
>     [Value f' _] -> Export f' : fromMaybe [] tcExport
>     [_] -> fromMaybe (errorAt p (exportDataConstr f)) tcExport
>     _ -> errorAt p (ambiguousName f)

> expandTypeWith :: Position -> TCEnv -> QualIdent -> [Ident] -> Export
> expandTypeWith p tcEnv tc cs =
>   case qualLookupTC tc tcEnv of
>     [] -> errorAt p (undefinedType tc)
>     [t]
>       | isDataType t -> ExportTypeWith (origName t)
>                           (map (checkConstr (constrs t)) (nub cs))
>       | otherwise -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)
>   where checkConstr cs c
>           | c `elem` cs = c
>           | otherwise = errorAt p (undefinedDataConstr tc c)

> expandTypeAll :: Position -> TCEnv -> QualIdent -> Export
> expandTypeAll p tcEnv tc =
>   case qualLookupTC tc tcEnv of
>     [] -> errorAt p (undefinedType tc)
>     [t]
>       | isDataType t -> exportType t 
>       | otherwise -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)

> expandLocalModule :: TCEnv -> ValueEnv -> [Export]
> expandLocalModule tcEnv tyEnv =
>   [exportType t | (_,t) <- localBindings tcEnv] ++
>   [Export f' | (f,Value f' _) <- localBindings tyEnv, f == unRenameIdent f]

> expandModule :: TCEnv -> ValueEnv -> ModuleIdent -> [Export]
> expandModule tcEnv tyEnv m =
>   [exportType t | (_,t) <- moduleImports m tcEnv] ++
>   [Export f | (_,Value f _) <- moduleImports m tyEnv]

> exportType :: TypeInfo -> Export
> exportType t = ExportTypeWith (origName t) (constrs t)

\end{verbatim}
The expanded list of exported entities may contain duplicates. These
are removed by the function \texttt{nubExports}.
\begin{verbatim}

> nubExports :: [Export] -> [Export]
> nubExports es =
>   [ExportTypeWith tc cs | (tc,cs) <- toListFM (foldr addType zeroFM es)] ++
>   [Export f | f <- toListSet (foldr addFun zeroSet es)]

> addType :: Export -> FM QualIdent [Ident] -> FM QualIdent [Ident]
> addType (Export _) tcs = tcs
> addType (ExportTypeWith tc cs) tcs =
>   addToFM tc (cs `union` fromMaybe [] (lookupFM tc tcs)) tcs

> addFun :: Export -> Set QualIdent -> Set QualIdent
> addFun (Export f) fs = f `addToSet` fs
> addFun (ExportTypeWith _ _) fs = fs

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> isDataType :: TypeInfo -> Bool
> isDataType (DataType _ _ _) = True
> isDataType (RenamingType _ _ _) = True
> isDataType (AliasType _ _ _) = False

> constrs :: TypeInfo -> [Ident]
> constrs (DataType _ _ cs) = [c | Just (Data c _ _) <- cs]
> constrs (RenamingType _ _ (Data c _ _)) = [c]
> constrs (AliasType _ _ _) = []

\end{verbatim}
Error messages:
\begin{verbatim}

> undefinedEntity :: QualIdent -> String
> undefinedEntity x =
>   "Entity " ++ qualName x ++ " in export list is not defined"

> undefinedType :: QualIdent -> String
> undefinedType tc = "Type " ++ qualName tc ++ " in export list is not defined"

> moduleNotImported :: ModuleIdent -> String
> moduleNotImported m = "Module " ++ moduleName m ++ " not imported"

> ambiguousExportType :: Ident -> String
> ambiguousExportType x = "Ambiguous export of type " ++ name x

> ambiguousExportValue :: Ident -> String
> ambiguousExportValue x = "Ambiguous export of " ++ name x

> ambiguousType :: QualIdent -> String
> ambiguousType tc = "Ambiguous type " ++ qualName tc

> ambiguousName :: QualIdent -> String
> ambiguousName x = "Ambiguous name " ++ qualName x

> exportDataConstr :: QualIdent -> String
> exportDataConstr c = "Data constructor " ++ qualName c ++ " in export list"

> nonDataType :: QualIdent -> String
> nonDataType tc = qualName tc ++ " is not a data type"

> undefinedDataConstr :: QualIdent -> Ident -> String
> undefinedDataConstr tc c =
>   name c ++ " is not a data constructor of type " ++ qualName tc

\end{verbatim}
