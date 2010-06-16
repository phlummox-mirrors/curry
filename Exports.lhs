% -*- LaTeX -*-
% $Id: Exports.lhs 2963 2010-06-16 16:42:38Z wlux $
%
% Copyright (c) 2000-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Exports.lhs}
\section{Creating Interfaces}\label{sec:exports}
After checking a module, the compiler generates the interface's
declarations from the list of exported types and values. If an entity
is imported from another module, its name is qualified with the name
of the module containing its definition.

Data types whose constructors are not exported are exported as
abstract types, i.e., their data constructors do not appear in the
interface. If only some data constructors of a data type are not
exported those constructors appear in the interface together with the
exported constructors, but a pragma marks them as hidden so that they
cannot be used in user code. A special case is made for the Prelude's
\texttt{Success} type, whose only constructor is not exported from the
Prelude. Since the compiler makes use of this constructor when
flattening guard expressions (cf.\ Sect.~\ref{sec:flatcase}),
\texttt{typeDecl}'s \texttt{DataType} case explicitly forces the
\texttt{Success} constructor to appear as hidden data constructor in
the interface.

\textbf{Attention:} The compiler assumes that the environments passed
to \texttt{exportInterface} reflect the types of the module's entities
after type inference. However, the source code module passed to
\texttt{exportInterface} must reflect the module's code \emph{after}
applying all source code transformations to the program.
\begin{verbatim}

> module Exports(exportInterface) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import IntfQual
> import List
> import Maybe
> import Monad
> import PrecInfo
> import PredefIdent
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

> exportInterface :: Module a -> PEnv -> TCEnv -> ValueEnv -> Interface
> exportInterface (Module m (Just (Exporting _ es)) _ ds) pEnv tcEnv tyEnv =
>   Interface m imports (unqualIntf m (precs ++ hidden ++ ds'))
>   where aEnv = bindArities m ds
>         tcs = foldr definedType [] ds'
>         tcs' = hiddenTypes ds' tcs
>         tcs'' = [tc | Just tc <- map (localIdent m) (tcs ++ tcs')]
>         tvs = filter (`notElem` tcs'') nameSupply
>         imports = map (IImportDecl noPos) (filter (m /=) (usedModules ds'))
>         precs = foldr (infixDecl pEnv) [] es
>         hidden = map (hiddenTypeDecl tcEnv tvs) tcs'
>         ds' =
>           foldr (typeDecl tcEnv tyEnv tvs)
>                 (foldr (valueDecl aEnv tyEnv tvs) [] es)
>                 es

> infixDecl :: PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl pEnv (Export f) ds = iInfixDecl pEnv f ds
> infixDecl pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl pEnv . qualifyLike tc) ds cs

> iInfixDecl :: PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl pEnv op ds =
>   case qualLookupTopEnv op pEnv of
>     [] -> ds
>     [PrecInfo _ (OpPrec fix pr)] -> IInfixDecl noPos fix pr op : ds
>     _ -> internalError "infixDecl"

> typeDecl :: TCEnv -> ValueEnv -> [Ident] -> Export -> [IDecl] -> [IDecl]
> typeDecl _ _ _ (Export _) ds = ds
> typeDecl tcEnv tyEnv tvs (ExportTypeWith tc xs) ds =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ n cs] -> iTypeDecl IDataDecl tc tvs n constrs xs' : ds
>       where constrs = guard vis >> cs'
>             xs' = guard vis >> filter (`notElem` xs) (cs ++ ls)
>             cs' = map (constrDecl tyEnv xs tc tvs n) cs
>             ls = nub (concatMap labels cs')
>             vis = not (null xs) || tc == qSuccessId
>     [RenamingType _ n c] -> iTypeDecl INewtypeDecl tc tvs n nc xs' : ds
>       where nc = newConstrDecl tyEnv xs tc tvs c
>             xs' = [c | c `notElem` xs]
>     [AliasType _ n ty] -> iTypeDecl ITypeDecl tc tvs n (fromType tvs ty) : ds
>     _ -> internalError "typeDecl"

> iTypeDecl :: (Position -> QualIdent -> [Ident] -> a)
>           -> QualIdent -> [Ident] -> Int -> a
> iTypeDecl f tc tvs n = f noPos tc (take n tvs)

> constrDecl :: ValueEnv -> [Ident] -> QualIdent -> [Ident] -> Int -> Ident
>            -> ConstrDecl
> constrDecl tyEnv xs tc tvs n c
>   | any (`elem` xs) ls = RecordDecl noPos evs c fs
>   | otherwise = ConstrDecl noPos evs c tys
>   where evs = drop n (take n' tvs)
>         (ls,ForAll n' ty) = conType (qualifyLike tc c) tyEnv
>         tys = map (fromType tvs) (arrowArgs ty)
>         fs = zipWith (FieldDecl noPos . return) ls tys

> newConstrDecl :: ValueEnv -> [Ident] -> QualIdent -> [Ident] -> Ident
>               -> NewConstrDecl
> newConstrDecl tyEnv xs tc tvs c
>   | l `elem` xs = NewRecordDecl noPos c l ty'
>   | otherwise = NewConstrDecl noPos c ty'
>   where (l:_,ForAll _ ty) = conType (qualifyLike tc c) tyEnv
>         ty' = fromType tvs (head (arrowArgs ty))

> valueDecl :: ArityEnv -> ValueEnv -> [Ident] -> Export -> [IDecl] -> [IDecl]
> valueDecl aEnv tyEnv tvs (Export f) ds =
>   IFunctionDecl noPos f n' (fromType tvs ty) : ds
>   where n = fromMaybe (arity f tyEnv) (lookupEnv f aEnv)
>         n' = if arrowArity ty == n then Nothing else Just (toInteger n)
>         ForAll _ ty = funType f tyEnv
> valueDecl _ _ _ (ExportTypeWith _ _) ds = ds

\end{verbatim}
Simplification can change the arity of an exported function defined in
the current module via $\eta$-expansion (cf.\ 
Sect.~\ref{eta-expansion}). In order to generate correct arity
annotations, the compiler collects the arities of all user defined
functions at the top-level of the transformed code in an auxiliary
environment. Note that we ignore foreign function declarations here
because their arities are fixed and cannot be changed by program
transformations.
\begin{verbatim}

> type ArityEnv = Env QualIdent Int

> bindArities :: ModuleIdent -> [TopDecl a] -> ArityEnv
> bindArities m ds = foldr (uncurry (bindEnv . qualifyWith m)) emptyEnv $
>   [(f,eqnArity (head eqs)) | BlockDecl (FunctionDecl _ _ f eqs) <- ds]

\end{verbatim}
The compiler determines the list of imported modules from the set of
module qualifiers that are used in the interface. Note that the list
of modules returned from \texttt{usedModules} is not necessarily a
subset of the union of the current module and the modules that were
imported into it. This will happen when an imported module reexports
entities from another module. E.g., given the three modules
\begin{verbatim}
module A where { data A = A; }
module B(A(..)) where { import A; }
module C where { import B; x = A; }
\end{verbatim}
the interface for module \texttt{C} will import module \texttt{A} but
not module \texttt{B}.
\begin{verbatim}

> usedModules :: [IDecl] -> [ModuleIdent]
> usedModules ds = nub (modules ds [])
>   where nub = toListSet . fromListSet

> class HasModule a where
>   modules :: a -> [ModuleIdent] -> [ModuleIdent]

> instance HasModule a => HasModule (Maybe a) where
>   modules = maybe id modules

> instance HasModule a => HasModule [a] where
>   modules xs ms = foldr modules ms xs

> instance HasModule IDecl where
>   modules (IDataDecl _ tc _ cs _) = modules tc . modules cs
>   modules (INewtypeDecl _ tc _ nc _) = modules tc . modules nc
>   modules (ITypeDecl _ tc _ ty) = modules tc . modules ty
>   modules (IFunctionDecl _ f _ ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ _ tys) = modules tys
>   modules (ConOpDecl _ _ ty1 _ ty2) = modules ty1 . modules ty2
>   modules (RecordDecl _ _ _ fs) = modules fs

> instance HasModule FieldDecl where
>   modules (FieldDecl _ _ ty) = modules ty

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ ty) = modules ty
>   modules (NewRecordDecl _ _ _ ty) = modules ty

> instance HasModule TypeExpr where
>   modules (ConstructorType tc tys) = modules tc . modules tys
>   modules (VariableType _) = id
>   modules (TupleType tys) = modules tys
>   modules (ListType ty) = modules ty
>   modules (ArrowType ty1 ty2) = modules ty1 . modules ty2

> instance HasModule QualIdent where
>   modules = maybe id (:) . fst . splitQualIdent

\end{verbatim}
After the interface declarations have been computed, the compiler adds
hidden (data) type declarations to the interface for all types which
were used in the interface but are not exported from it. This is
necessary in order to distinguish type constructors and type
variables. Furthermore, by including hidden types in interfaces the
compiler can check them without loading the imported modules.
\begin{verbatim}

> hiddenTypeDecl :: TCEnv -> [Ident] -> QualIdent -> IDecl
> hiddenTypeDecl tcEnv tvs tc = HidingDataDecl noPos tc (take n tvs)
>   where n = constrKind tc tcEnv

> hiddenTypes :: [IDecl] -> [QualIdent] -> [QualIdent]
> hiddenTypes ds =
>   filter (not . isPrimTypeId . unqualify) .
>   toListSet . foldr deleteFromSet (fromListSet (usedTypes ds []))

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ tc _ _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _) tcs = tc : tcs
> definedType (IFunctionDecl _ _ _ _) tcs = tcs

> class HasType a where
>   usedTypes :: a -> [QualIdent] -> [QualIdent]

> instance HasType a => HasType (Maybe a) where
>   usedTypes = maybe id usedTypes

> instance HasType a => HasType [a] where
>   usedTypes xs tcs = foldr usedTypes tcs xs

> instance HasType IDecl where
>   usedTypes (IDataDecl _ _ _ cs _) = usedTypes cs
>   usedTypes (INewtypeDecl _ _ _ nc _) = usedTypes nc
>   usedTypes (ITypeDecl _ _ _ ty) = usedTypes ty
>   usedTypes (IFunctionDecl _ _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ _ tys) = usedTypes tys
>   usedTypes (ConOpDecl _ _ ty1 _ ty2) = usedTypes ty1 . usedTypes ty2
>   usedTypes (RecordDecl _ _ _ fs) = usedTypes fs

> instance HasType FieldDecl where
>   usedTypes (FieldDecl _ _ ty) = usedTypes ty

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ ty) = usedTypes ty
>   usedTypes (NewRecordDecl _ _ _ ty) = usedTypes ty

> instance HasType TypeExpr where
>   usedTypes (ConstructorType tc tys) = (tc :) . usedTypes tys
>   usedTypes (VariableType _) = id
>   usedTypes (TupleType tys) = usedTypes tys
>   usedTypes (ListType ty) = usedTypes ty
>   usedTypes (ArrowType ty1 ty2) = usedTypes ty1 . usedTypes ty2

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> noPos :: Position
> noPos = undefined

\end{verbatim}
