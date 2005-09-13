% -*- LaTeX -*-
% $Id: ExportSyntaxCheck.lhs 1766 2005-09-13 15:26:29Z wlux $
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

> checkExports :: ModuleIdent -> [ImportDecl] -> TypeEnv -> FunEnv
>              -> Maybe ExportSpec -> ExportSpec
> checkExports m is tEnv fEnv es = Exporting noPos $
>   maybe (expandLocalModule tEnv fEnv)
>         (checkInterface . nubExports . expandSpecs ms m tEnv fEnv)
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

> expandSpecs :: Set ModuleIdent -> ModuleIdent -> TypeEnv -> FunEnv
>             -> ExportSpec -> [Export]
> expandSpecs ms m tEnv fEnv (Exporting p es) =
>   concat (map (expandExport p ms m tEnv fEnv) es)

> expandExport :: Position -> Set ModuleIdent -> ModuleIdent -> TypeEnv
>              -> FunEnv -> Export -> [Export]
> expandExport p _ _ tEnv fEnv (Export x) = expandThing p tEnv fEnv x
> expandExport p _ _ tEnv _ (ExportTypeWith tc cs) =
>   [expandTypeWith p tEnv tc cs]
> expandExport p _ _ tEnv _ (ExportTypeAll tc) = [expandTypeAll p tEnv tc]
> expandExport p ms m tEnv fEnv (ExportModule m')
>   | m == m' = (if m `elemSet` ms then expandModule tEnv fEnv m else [])
>               ++ expandLocalModule tEnv fEnv
>   | m' `elemSet` ms = expandModule tEnv fEnv m'
>   | otherwise = errorAt p (moduleNotImported m')

> expandThing :: Position -> TypeEnv -> FunEnv -> QualIdent -> [Export]
> expandThing p tEnv fEnv tc =
>   case qualLookupType tc tEnv of
>     [] -> expandThing' p fEnv tc Nothing
>     [t] -> expandThing' p fEnv tc (Just [exportType (abstract t)])
>       where abstract (Data tc n _) = Data tc n []
>             abstract (Alias tc n) = Alias tc n
>     _ -> errorAt p (ambiguousType tc)

> expandThing' :: Position -> FunEnv -> QualIdent -> Maybe [Export] -> [Export]
> expandThing' p fEnv f tcExport =
>   case qualLookupFun f fEnv of
>     [] -> fromMaybe (errorAt p (undefinedEntity f)) tcExport
>     [Var f'] -> Export f' : fromMaybe [] tcExport
>     [Constr _ _] -> fromMaybe (errorAt p (exportDataConstr f)) tcExport
>     _ -> errorAt p (ambiguousName f)

> expandTypeWith :: Position -> TypeEnv -> QualIdent -> [Ident] -> Export
> expandTypeWith p tEnv tc cs =
>   case qualLookupType tc tEnv of
>     [] -> errorAt p (undefinedType tc)
>     [Data tc' _ cs'] -> ExportTypeWith tc' (map (checkConstr cs') (nub cs))
>     [Alias _ _] -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)
>   where checkConstr cs c
>           | c `elem` cs = c
>           | otherwise = errorAt p (undefinedDataConstr tc c)

> expandTypeAll :: Position -> TypeEnv -> QualIdent -> Export
> expandTypeAll p tEnv tc =
>   case qualLookupType tc tEnv of
>     [] -> errorAt p (undefinedType tc)
>     [Data tc' _ cs'] -> ExportTypeWith tc' cs'
>     [Alias _ _] -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)

> expandLocalModule :: TypeEnv -> FunEnv -> [Export]
> expandLocalModule tEnv fEnv =
>   [exportType t | (_,t) <- localBindings tEnv] ++
>   [Export f' | (f,Var f') <- localBindings fEnv, f == unRenameIdent f]

> expandModule :: TypeEnv -> FunEnv -> ModuleIdent -> [Export]
> expandModule tEnv fEnv m =
>   [exportType t | (_,t) <- moduleImports m tEnv] ++
>   [Export f | (_,Var f) <- moduleImports m fEnv]

> exportType :: TypeKind -> Export
> exportType (Data tc _ cs) = ExportTypeWith tc cs
> exportType (Alias tc _) = ExportTypeWith tc []

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
