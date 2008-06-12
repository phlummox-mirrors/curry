% -*- LaTeX -*-
% $Id: ImportSyntaxCheck.lhs 2718 2008-06-12 14:04:58Z wlux $
%
% Copyright (c) 2000-2008, Wolfgang Lux
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
> import Curry
> import CurryUtils
> import Error
> import Env
> import IdentInfo
> import List
> import Maybe
> import PredefIdent

> checkImports :: Interface -> Maybe ImportSpec -> Error (Maybe ImportSpec)
> checkImports (Interface m _ ds) =
>   maybe (return Nothing) (liftE Just . expandSpecs m tEnv vEnv)
>   where tEnv = foldr bindType emptyEnv ds
>         vEnv = foldr bindValue emptyEnv ds

\end{verbatim}
The compiler uses two environments collecting the type and value
identifiers, respectively, declared in the interface. In a first step,
the two export environments are initialized from the interface's
declarations.
\begin{verbatim}

> type ExpTypeEnv = Env Ident TypeKind
> type ExpFunEnv = Env Ident ValueKind

> bindType :: IDecl -> ExpTypeEnv -> ExpTypeEnv
> bindType (IDataDecl _ tc _ cs xs') = bindData tc xs' xs
>   where xs = map constr cs ++ nub (concatMap labels cs)
> bindType (INewtypeDecl _ tc _ nc xs') = bindData tc xs' xs
>   where xs = nconstr nc : nlabel nc
> bindType (ITypeDecl _ tc _ _) = bindAlias tc
> bindType _ = id

> bindData :: QualIdent -> [Ident] -> [Ident] -> ExpTypeEnv -> ExpTypeEnv
> bindData tc xs' xs = bindUnqual tc (Data tc (filter (`notElem` xs') xs))

> bindAlias :: QualIdent -> ExpTypeEnv -> ExpTypeEnv
> bindAlias tc = bindUnqual tc (Alias tc)

> bindValue :: IDecl -> ExpFunEnv -> ExpFunEnv
> bindValue (IDataDecl _ tc _ cs xs) =
>   bindConstrs tc xs (map constr cs) .
>   bindLabels tc xs [(l,constrs cs l) | l <- nub (concatMap labels cs)]
>   where constrs cs l = [constr c | c <- cs, l `elem` labels c]
> bindValue (INewtypeDecl _ tc _ nc xs) =
>   bindConstrs tc xs [nconstr nc] .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l _ -> bindLabels tc xs [(l,[c])]
> bindValue (IFunctionDecl _ f _ _) = bindFun f
> bindValue _ = id

> bindConstrs :: QualIdent -> [Ident] -> [Ident] -> ExpFunEnv -> ExpFunEnv
> bindConstrs tc xs cs env =
>   foldr (bindConstr tc) env (filter (`notElem` xs) cs)

> bindConstr :: QualIdent -> Ident -> ExpFunEnv -> ExpFunEnv
> bindConstr tc c = bindEnv c (Constr (qualifyLike tc c))

> bindLabels :: QualIdent -> [Ident] -> [(Ident,[Ident])] -> ExpFunEnv
>            -> ExpFunEnv
> bindLabels tc xs ls env =
>   foldr (uncurry (bindLabel tc)) env (filter ((`notElem` xs) . fst) ls)

> bindLabel :: QualIdent -> Ident -> [Ident] -> ExpFunEnv -> ExpFunEnv
> bindLabel tc l cs =
>   bindEnv l (Var (qualifyLike tc l) (map (qualifyLike tc) cs))

> bindFun :: QualIdent -> ExpFunEnv -> ExpFunEnv
> bindFun f = bindUnqual f (Var f [])

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
data constructors are added. The code of \texttt{expandSpecs} ensures
that the unit, list, and tuple types are always imported from the
Prelude even if its imported entities are specified explicitly.
\begin{verbatim}

> expandSpecs :: ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> ImportSpec
>             -> Error ImportSpec
> expandSpecs m tEnv vEnv (Importing p is) =
>   liftE (Importing p . (is' ++) . concat)
>         (mapE (expandImport p m tEnv vEnv) is)
>   where is' = [importType t | m == preludeMIdent,
>                               (tc,t) <- envToList tEnv, isPrimTypeId tc]
> expandSpecs m tEnv vEnv (Hiding p is) =
>   liftE (Hiding p . concat) (mapE (expandHiding p m tEnv vEnv) is)

> expandImport :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Import
>              -> Error [Import]
> expandImport p m tEnv vEnv (Import x) = expandThing p m tEnv vEnv x
> expandImport p m tEnv vEnv (ImportTypeWith tc xs) =
>   expandTypeWith p m tEnv tc xs
> expandImport p m tEnv vEnv (ImportTypeAll tc) = expandTypeAll p m tEnv tc

> expandHiding :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Import
>              -> Error [Import]
> expandHiding p m tEnv vEnv (Import x) = expandHide p m tEnv vEnv x
> expandHiding p m tEnv vEnv (ImportTypeWith tc xs) =
>   expandTypeWith p m tEnv tc xs
> expandHiding p m tEnv vEnv (ImportTypeAll tc) = expandTypeAll p m tEnv tc

> expandThing :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Ident
>             -> Error [Import]
> expandThing p m tEnv vEnv tc =
>   case lookupEnv tc tEnv of
>     Just _ -> expandThing' p m vEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandThing' p m vEnv tc Nothing

> expandThing' :: Position -> ModuleIdent -> ExpFunEnv -> Ident
>              -> Maybe [Import] -> Error [Import]
> expandThing' p m vEnv f tcImport =
>   case lookupEnv f vEnv of
>     Just (Constr _) -> maybe (errorAt p (importDataConstr f)) return tcImport
>     Just (Var _ _) -> return (Import f : fromMaybe [] tcImport)
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) return tcImport

> expandHide :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Ident
>            -> Error [Import]
> expandHide p m tEnv vEnv tc =
>   case lookupEnv tc tEnv of
>     Just _ -> expandHide' p m vEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandHide' p m vEnv tc Nothing

> expandHide' :: Position -> ModuleIdent -> ExpFunEnv -> Ident
>             -> Maybe [Import] -> Error [Import]
> expandHide' p m vEnv f tcImport =
>   case lookupEnv f vEnv of
>     Just _ -> return (Import f : fromMaybe [] tcImport)
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) return tcImport

> expandTypeWith :: Position -> ModuleIdent -> ExpTypeEnv -> Ident -> [Ident]
>                -> Error [Import]
> expandTypeWith p m tEnv tc xs =
>   do
>     xs'' <- elements p m tEnv tc
>     mapE_ (errorAt p . undefinedElement tc) (filter (`notElem` xs'') xs')
>     return [ImportTypeWith tc xs']
>   where xs' = nub xs

> expandTypeAll :: Position -> ModuleIdent -> ExpTypeEnv -> Ident
>               -> Error [Import]
> expandTypeAll p m tEnv tc =
>   do
>     xs <- elements p m tEnv tc
>     return [ImportTypeWith tc xs]

> elements :: Position -> ModuleIdent -> ExpTypeEnv -> Ident -> Error [Ident]
> elements p m tEnv tc =
>   case lookupEnv tc tEnv of
>     Just (Data _ xs) -> return xs
>     Just (Alias _) -> return []
>     Nothing -> errorAt p (undefinedType m tc)

> importType :: TypeKind -> Import
> importType (Data tc xs) = ImportTypeWith (unqualify tc) xs
> importType (Alias tc) = ImportTypeWith (unqualify tc) []

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedEntity :: ModuleIdent -> Ident -> String
> undefinedEntity m x =
>   "Module " ++ moduleName m ++ " does not export " ++ name x

> undefinedType :: ModuleIdent -> Ident -> String
> undefinedType m tc =
>   "Module " ++ moduleName m ++ " does not export type " ++ name tc

> undefinedElement :: Ident -> Ident -> String
> undefinedElement tc c =
>   name c ++ " is not a constructor or label of type " ++ name tc

> importDataConstr :: Ident -> String
> importDataConstr c = "Explicit import of data constructor " ++ name c

\end{verbatim}
