% -*- LaTeX -*-
% $Id: ExportSyntaxCheck.lhs 1780 2005-10-03 18:54:07Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ExportSyntaxCheck.lhs}
\section{Checking Module Export Lists}
The function \texttt{checkExports} checks the export specifications of
the module and expands them into a list containing all exported types
and functions, combining multiple exports for the same entity. The
expanded export specifications refer to the original names of all
entities.
\begin{verbatim}

> module ExportSyntaxCheck(checkExports) where
> import Base
> import Error
> import List
> import Map
> import Maybe
> import Monad
> import Set
> import TopEnv

> checkExports :: ModuleIdent -> [ImportDecl] -> TypeEnv -> FunEnv
>              -> Maybe ExportSpec -> Error ExportSpec
> checkExports m is tEnv fEnv =
>   maybe (return (Exporting noPos (expandLocalModule tEnv fEnv)))
>         (\es -> do
>                   es' <- liftM nubExports (expandSpecs ms m tEnv fEnv es)
>                   checkInterface es'
>                   return es')
>   where ms = fromListSet [fromMaybe m asM | ImportDecl _ m _ asM _ <- is]
>         noPos = undefined

> checkInterface :: ExportSpec -> Error ()
> checkInterface (Exporting p es) =
>   case linear [unqualify tc | ExportTypeWith tc _ <- es] of
>     Linear ->
>       case linear ([c | ExportTypeWith _ cs <- es, c <- cs] ++
>                    [unqualify f | Export f <- es]) of
>         Linear -> return ()
>         NonLinear v -> errorAt p (ambiguousExportValue v)
>     NonLinear tc -> errorAt p (ambiguousExportType tc)

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
>             -> ExportSpec -> Error ExportSpec
> expandSpecs ms m tEnv fEnv (Exporting p es) =
>   liftM (Exporting p . concat) (mapM (expandExport p ms m tEnv fEnv) es)

> expandExport :: Position -> Set ModuleIdent -> ModuleIdent -> TypeEnv
>              -> FunEnv -> Export -> Error [Export]
> expandExport p _ _ tEnv fEnv (Export x) = expandThing p tEnv fEnv x
> expandExport p _ _ tEnv _ (ExportTypeWith tc cs) = expandTypeWith p tEnv tc cs
> expandExport p _ _ tEnv _ (ExportTypeAll tc) = expandTypeAll p tEnv tc
> expandExport p ms m tEnv fEnv (ExportModule m')
>   | m == m' =
>       return ((if m `elemSet` ms then expandModule tEnv fEnv m else []) ++
>               expandLocalModule tEnv fEnv)
>   | m' `elemSet` ms = return (expandModule tEnv fEnv m')
>   | otherwise = errorAt p (moduleNotImported m')

> expandThing :: Position -> TypeEnv -> FunEnv -> QualIdent -> Error [Export]
> expandThing p tEnv fEnv tc =
>   case qualLookupType tc tEnv of
>     [] -> expandThing' p fEnv tc Nothing
>     [t] -> expandThing' p fEnv tc (Just [exportType (abstract t)])
>       where abstract (Data tc _) = Data tc []
>             abstract (Alias tc) = Alias tc
>     _ -> errorAt p (ambiguousType tc)

> expandThing' :: Position -> FunEnv -> QualIdent -> Maybe [Export]
>              -> Error [Export]
> expandThing' p fEnv f tcExport =
>   case qualLookupFun f fEnv of
>     [] -> maybe (errorAt p (undefinedEntity f)) return tcExport
>     [Var f'] -> return (Export f' : fromMaybe [] tcExport)
>     [Constr _ _] -> maybe (errorAt p (exportDataConstr f)) return tcExport
>     _ -> errorAt p (ambiguousName f)

> expandTypeWith :: Position -> TypeEnv -> QualIdent -> [Ident]
>                -> Error [Export]
> expandTypeWith p tEnv tc cs =
>   case qualLookupType tc tEnv of
>     [] -> errorAt p (undefinedType tc)
>     [Data tc' cs'] ->
>       do
>         checkConstrs cs' cs''
>         return [ExportTypeWith tc' cs'']
>     [Alias _] -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)
>   where cs'' = nub cs
>         checkConstrs cs' cs =
>           case filter (`notElem` cs') cs of
>             [] -> return ()
>             c:_ -> errorAt p (undefinedDataConstr tc c)

> expandTypeAll :: Position -> TypeEnv -> QualIdent -> Error [Export]
> expandTypeAll p tEnv tc =
>   case qualLookupType tc tEnv of
>     [] -> errorAt p (undefinedType tc)
>     [Data tc' cs'] -> return [ExportTypeWith tc' cs']
>     [Alias _] -> errorAt p (nonDataType tc)
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
> exportType (Data tc cs) = ExportTypeWith tc cs
> exportType (Alias tc) = ExportTypeWith tc []

\end{verbatim}
The expanded list of exported entities may contain duplicates. These
are removed by the function \texttt{nubExports}.
\begin{verbatim}

> nubExports :: ExportSpec -> ExportSpec
> nubExports (Exporting p es) = Exporting p $
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
Error messages.
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
