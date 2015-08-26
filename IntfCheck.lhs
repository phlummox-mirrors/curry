% -*- LaTeX -*-
% $Id: IntfCheck.lhs 3169 2015-08-26 19:34:38Z wlux $
%
% Copyright (c) 2000-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfCheck.lhs}
\section{Interface Consistency Checks}
Interface files include declarations of all entities that are exported
by the module but defined in another module. Since these declarations
can become inconsistent if client modules are not recompiled properly,
the compiler checks that all imported declarations in interfaces are
consistent and agree with their original definitions where they are
available.

The main rationale for this design decision is that it is sufficient
to read only the interfaces of the Prelude and those modules that are
imported explicitly by the compiled module if the definitions of all
exported entities are present in an interface. This makes
bootstrapping simpler for mutually recursive modules, in particular if
the mutual recursion also shows up in the interfaces. Furthermore, it
helps avoiding unnecessary recompilation of client modules. As an
example, consider the three modules
\begin{verbatim}
  module A where { data T = C }
  module B(T(..)) where { import A }
  module C where { import B; f = C }
\end{verbatim}
where module \texttt{B} could be considered the public interface of
module \texttt{A}, which restricts access to type \texttt{A.T} and its
constructor \texttt{C}. The client module \texttt{C} imports this type
via the public interface \texttt{B}. If now module \texttt{A} is
changed by adding a definition of a new global function
\begin{verbatim}
  module A where { data T = C; f = C }
\end{verbatim}
module \texttt{B} must be recompiled because \texttt{A}'s interface is
changed. On the other hand, module \texttt{C} need not be recompiled
because the change in \texttt{A} does not affect \texttt{B}'s
interface. By including the declaration of type \texttt{A.T} in
\texttt{B}'s interface, the compiler can trivially check that
\texttt{B}'s interface remains unchanged and therefore the client
module \texttt{C} is not recompiled.

When detecting a conflict between the definition of an imported
entity, say \texttt{A.x}, in the interfaces of modules \texttt{B} and
\texttt{C}, respectively, we have to distinguish whether the interface
of module \texttt{A} has been loaded as well or not. In the former
case, we can give an authoritative answer whether \texttt{A.x}'s
definition in \texttt{B} is wrong or whether the definition in
\texttt{C} is wrong. We can even detect if \texttt{A} does not export
\texttt{x} at all. In the latter case, we can not give an
authoritative answer which definition is wrong and therefore report an
error for both.
\begin{verbatim}

> module IntfCheck(intfCheck) where
> import Applicative()
> import Base
> import Curry
> import CurryUtils
> import Error
> import Maybe
> import Monad
> import PrecInfo
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import Utils
> import ValueInfo

> intfCheck :: ModuleIdent -> PEnv -> TCEnv -> ValueEnv -> [IDecl] -> Error ()
> intfCheck m pEnv tcEnv tyEnv ds =
>   mapA_ (checkImport pEnv tcEnv tyEnv)
>         (filter (isNothing . localIdent m . entity) ds)

> checkImport :: PEnv -> TCEnv -> ValueEnv -> IDecl -> Error ()
> checkImport pEnv _ _ (IInfixDecl p fix pr op) =
>   checkPrecInfo checkPrec pEnv p op
>   where checkPrec (PrecInfo op' (OpPrec fix' pr')) =
>           op == op' && fix == fix' && pr == pr'
> checkImport _ tcEnv _ (HidingDataDecl p tc tvs) =
>   checkTypeInfo "hidden data type" checkData tcEnv p tc
>   where checkData (DataType tc' n' _)
>           | tc == tc' && length tvs == n' = Just (return ())
>         checkData (RenamingType tc' n' _)
>           | tc == tc' && length tvs == n' = Just (return ())
>         checkData _ = Nothing
> checkImport _ tcEnv tyEnv (IDataDecl p tc tvs cs _) =
>   checkTypeInfo "data type" checkData tcEnv p tc
>   where checkData (DataType tc' n' cs')
>           | tc == tc' && length tvs == n' &&
>             (null cs || map constr cs == cs') =
>               Just (mapM_ (checkConstrImport tyEnv tc tvs) cs)
>         checkData (RenamingType tc' n' _)
>           | tc == tc' && length tvs == n' && null cs = Just (return ())
>         checkData _ = Nothing
> checkImport _ tcEnv tyEnv (INewtypeDecl p tc tvs nc _) =
>   checkTypeInfo "newtype" checkNewtype tcEnv p tc
>   where checkNewtype (RenamingType tc' n' nc')
>           | tc == tc' && length tvs == n' && nconstr nc == nc' =
>               Just (checkNewConstrImport tyEnv tc tvs nc)
>         checkNewtype _ = Nothing
> checkImport _ tcEnv _ (ITypeDecl p tc tvs ty) =
>   checkTypeInfo "synonym type" checkType tcEnv p tc
>   where checkType (AliasType tc' n' ty')
>           | tc == tc' && length tvs == n' && toType tvs ty == ty' =
>               Just (return ())
>         checkType _ = Nothing
> checkImport _ _ tyEnv (IFunctionDecl p f n ty) =
>   checkValueInfo "function" checkFun tyEnv p f
>   where checkFun (Value f' n' (ForAll _ ty')) =
>           f == f' && maybe True (toInteger n' ==) n && toType [] ty == ty'
>         checkFun _ = False

> checkConstrImport :: ValueEnv -> QualIdent -> [Ident] -> ConstrDecl
>                   -> Error ()
> checkConstrImport tyEnv tc tvs (ConstrDecl p evs c tys) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkConstr (DataConstructor c' _ (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toTypes tvs tys == arrowArgs ty'
>         checkConstr _ = False
> checkConstrImport tyEnv tc tvs (ConOpDecl p evs ty1 op ty2) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc op
>         checkConstr (DataConstructor c' _ (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toTypes tvs [ty1,ty2] == arrowArgs ty'
>         checkConstr _ = False
> checkConstrImport tyEnv tc tvs (RecordDecl p evs c fs) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         (ls,tys) = unzip [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls]
>         checkConstr (DataConstructor c' ls' (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' && ls == ls' &&
>           toTypes tvs tys == arrowArgs ty'
>         checkConstr _ = False

> checkNewConstrImport :: ValueEnv -> QualIdent -> [Ident] -> NewConstrDecl
>                      -> Error ()
> checkNewConstrImport tyEnv tc tvs (NewConstrDecl p c ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' _ (ForAll n' ty')) =
>           qc == c' && length tvs == n' &&
>           toType tvs ty == head (arrowArgs ty')
>         checkNewConstr _ = False
> checkNewConstrImport tyEnv tc tvs (NewRecordDecl p c l ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' l' (ForAll n' ty')) =
>           qc == c' && length tvs == n' && l == l' &&
>           toType tvs ty == head (arrowArgs ty')
>         checkNewConstr _ = False

> checkPrecInfo :: (PrecInfo -> Bool) -> PEnv -> Position
>               -> QualIdent -> Error ()
> checkPrecInfo check pEnv p op = checkImported checkInfo op
>   where what = "precedence"
>         checkInfo m op' =
>           case qualLookupTopEnv op pEnv of
>             [] -> errorAt p (noPrecedence m op')
>             [pi] -> unless (check pi) (errorAt p (importConflict what m op'))
>             _ -> errorAt p (inconsistentImports what op)

> checkTypeInfo :: String -> (TypeInfo -> Maybe (Error ())) -> TCEnv -> Position
>               -> QualIdent -> Error ()
> checkTypeInfo what check tcEnv p tc = checkImported checkInfo tc
>   where checkInfo m tc' =
>           case qualLookupTopEnv tc tcEnv of
>             [] -> errorAt p (notExported what m tc')
>             [ti] ->
>               fromMaybe (errorAt p (importConflict what m tc')) (check ti)
>             _ -> errorAt p (inconsistentImports what tc)

> checkValueInfo :: String -> (ValueInfo -> Bool) -> ValueEnv -> Position
>                -> QualIdent -> Error ()
> checkValueInfo what check tyEnv p x = checkImported checkInfo x
>   where checkInfo m x' =
>           case qualLookupTopEnv x tyEnv of
>             [] -> errorAt p (notExported what m x')
>             [vi] -> unless (check vi) (errorAt p (importConflict what m x'))
>             _ -> errorAt p (inconsistentImports what x)

> checkImported :: (ModuleIdent -> Ident -> Error ()) -> QualIdent -> Error ()
> checkImported f x = uncurry (f . fromJust) (splitQualIdent x)

\end{verbatim}
Error messages.
\begin{verbatim}

> notExported :: String -> ModuleIdent -> Ident -> String
> notExported what m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not export " ++ what ++ " " ++ name x

> noPrecedence :: ModuleIdent -> Ident -> String
> noPrecedence m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not define a precedence for " ++ name x

> importConflict :: String -> ModuleIdent -> Ident -> String
> importConflict what m x =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of " ++ what ++ " " ++ name x ++
>   " does not match its definition in module " ++ moduleName m

> inconsistentImports :: String -> QualIdent -> String
> inconsistentImports what x =
>   "Inconsistent module interfaces\n" ++
>   "Found inconsistent declarations for imported " ++ what ++ " " ++ qualName x

\end{verbatim}
