% -*- LaTeX -*-
% $Id: Base.lhs 1786 2005-10-07 15:33:33Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Base.lhs}
\section{Common Definitions for the Compiler}
The module \texttt{Base} provides definitions that are commonly used
in various phases of the compiler.
\begin{verbatim}

> module Base(module Base,module Ident,module Position,module Types,
>             module CurrySyntax) where
> import Ident
> import Position
> import CurrySyntax
> import Types
> import Env
> import TopEnv
> import NestEnv
> import Maybe
> import Monad
> import Set
> import Utils

\end{verbatim}
\paragraph{Interfaces}
The compiler maintains a global environment holding all (directly or
indirectly) imported interfaces.
\begin{verbatim}

> type ModuleEnv = Env ModuleIdent Interface

> bindModule :: Interface -> ModuleEnv -> ModuleEnv
> bindModule (Interface m is ds) = bindEnv m (Interface m is ds)

> lookupModule :: ModuleIdent -> ModuleEnv -> Maybe Interface
> lookupModule = lookupEnv

\end{verbatim}
\paragraph{Type constructors}
For all defined types, the compiler must maintain kind information. At
present, Curry does not support type classes. Therefore, its type
language is first order and the only information that must be recorded
is the arity of each type. For algebraic data types and renaming types
the compiler also records all data constructors belonging to that
type, for alias types the expanded type expression is saved. In order
to manage the import and export of types, the names of the original
definitions are also recorded. On import, two types are considered
equal if their original names match.

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type. When only some
constructors of a data type are hidden, those constructors are
replaced by underscores in the interface.
\begin{verbatim}

> data TypeInfo = DataType QualIdent Int [Maybe Ident]
>               | RenamingType QualIdent Int Ident
>               | AliasType QualIdent Int Type
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _) = tc
>   merge (DataType tc n cs) (DataType tc' _ cs')
>     | tc == tc' = Just (DataType tc n (mergeData cs cs'))
>     where mergeData cs cs'
>             | null cs = cs'
>             | null cs' = cs
>             | otherwise = zipWith mplus cs cs'
>   merge (DataType tc n _) (RenamingType tc' _ nc)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (DataType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (RenamingType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (AliasType tc n ty) (AliasType tc' _ _)
>     | tc == tc' = Just (AliasType tc n ty)
>   merge _ _ = Nothing

\end{verbatim}
Types can only be defined at the top-level; no nested environments are
needed for them. Tuple types must be handled as a special case because
there is an infinite number of potential tuple types making it
impossible to insert them into the environment in advance.
\begin{verbatim}

> type TCEnv = TopEnv TypeInfo

> bindTypeInfo :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent
>              -> Ident -> [Ident] -> a -> TCEnv -> TCEnv
> bindTypeInfo f m tc tvs =
>   globalBindTopEnv m tc . f (qualifyWith m tc) (length tvs)

> lookupTC :: Ident -> TCEnv -> [TypeInfo]
> lookupTC tc tcEnv = lookupTopEnv tc tcEnv ++! lookupTupleTC tc

> qualLookupTC :: QualIdent -> TCEnv -> [TypeInfo]
> qualLookupTC tc tcEnv =
>   qualLookupTopEnv tc tcEnv ++! lookupTupleTC (unqualify tc)

> lookupTupleTC :: Ident -> [TypeInfo]
> lookupTupleTC tc = [tupleTCs !! (tupleArity tc - 2) | isTupleId tc]

> tupleTCs :: [TypeInfo]
> tupleTCs = map typeInfo [2..]
>   where typeInfo n = DataType (qualify c) n [Just c]
>           where c = tupleId n

\end{verbatim}
A simpler environment is used for checking the syntax of type
expressions, where only the original names and the data constructors
associated with each type are needed. Since synonym types are treated
differently in import and export lists, we distinguish data and
renaming types on one side and synonym types on the other side.
\begin{verbatim}

> type TypeEnv = TopEnv TypeKind
> data TypeKind =
>     Data QualIdent [Ident]
>   | Alias QualIdent
>   deriving (Eq,Show)

> typeKind :: TypeInfo -> TypeKind
> typeKind (DataType tc _ cs) = Data tc (catMaybes cs)
> typeKind (RenamingType tc _ c) = Data tc [c]
> typeKind (AliasType tc _ _) = Alias tc

> bindTop :: ModuleIdent -> Ident -> TypeKind -> TypeEnv -> TypeEnv
> bindTop = globalBindTopEnv

> lookupType :: Ident -> TypeEnv -> [TypeKind]
> lookupType = lookupTopEnv

> qualLookupType :: QualIdent -> TypeEnv -> [TypeKind]
> qualLookupType = qualLookupTopEnv

\end{verbatim}
\paragraph{Function and constructor types}
In order to test the type correctness of a module, the compiler needs
to determine the type of every data constructor, function, and
variable in the module. For the purpose of type checking, there is no
need to distinguish variables and functions. For all objects, their
original names and their types are saved. On import, two values are
considered equal if their original names match.
\begin{verbatim}

> data ValueInfo = DataConstructor QualIdent ExistTypeScheme
>                | NewtypeConstructor QualIdent ExistTypeScheme
>                | Value QualIdent TypeScheme
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor origName _) = origName
>   origName (NewtypeConstructor origName _) = origName
>   origName (Value origName _) = origName

\end{verbatim}
Even though value declarations may be nested, the compiler uses a flat
environment for saving type information. This is possible because all
identifiers are renamed by the compiler before it starts computing type
information. Again, we need special cases for handling tuple
constructors.
\begin{verbatim}

> type ValueEnv = TopEnv ValueInfo

> bindGlobalInfo :: (QualIdent -> a -> ValueInfo) -> ModuleIdent -> Ident -> a
>                -> ValueEnv -> ValueEnv
> bindGlobalInfo f m c ty = globalBindTopEnv m c (f (qualifyWith m c) ty)

> bindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> bindFun m f ty = bindTopEnv m f (Value (qualifyWith m f) ty)

> rebindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> rebindFun m f ty = rebindTopEnv m f (Value (qualifyWith m f) ty)

> lookupValue :: Ident -> ValueEnv -> [ValueInfo]
> lookupValue x tyEnv = lookupTopEnv x tyEnv ++! lookupTuple x

> qualLookupValue :: QualIdent -> ValueEnv -> [ValueInfo]
> qualLookupValue x tyEnv =
>   qualLookupTopEnv x tyEnv ++! lookupTuple (unqualify x)

> lookupTuple :: Ident -> [ValueInfo]
> lookupTuple c = [tupleDCs !! (tupleArity c - 2) | isTupleId c]

> tupleDCs :: [ValueInfo]
> tupleDCs = map dataInfo tupleTCs
>   where tvs = map typeVar [0..]
>         dataInfo (DataType c n _) =
>           DataConstructor c (ForAllExist n 0 (tupleConstrType (take n tvs)))
>         tupleConstrType tys = foldr TypeArrow (tupleType tys) tys

\end{verbatim}
A simpler kind of environment is used for syntax checking of
expressions. We only distinguish constructors and variables here. A
nested environment is used for syntax checking because it is performed
before renaming. However, only the top-level of this environment is
used in order to check the export list of a module.
\begin{verbatim}

> type FunEnv = TopEnv ValueKind
> type VarEnv = NestEnv ValueKind
> data ValueKind = Constr QualIdent | Var QualIdent deriving (Eq,Show)

> valueKind :: ValueInfo -> ValueKind
> valueKind (DataConstructor c _) = Constr c
> valueKind (NewtypeConstructor c _) = Constr c
> valueKind (Value v _) = Var v

> bindGlobal :: ModuleIdent -> Ident -> ValueKind -> VarEnv -> VarEnv
> bindGlobal m c v = globalBindNestEnv m c v

> bindLocal :: Ident -> ValueKind -> VarEnv -> VarEnv
> bindLocal = localBindNestEnv

> lookupVar :: Ident -> VarEnv -> [ValueKind]
> lookupVar v env = lookupNestEnv v env ++! lookupTupleConstr v

> qualLookupVar :: QualIdent -> VarEnv -> [ValueKind]
> qualLookupVar v env =
>   qualLookupNestEnv v env ++! lookupTupleConstr (unqualify v)

> qualLookupFun :: QualIdent -> FunEnv -> [ValueKind]
> qualLookupFun f env =
>   qualLookupTopEnv f env ++! lookupTupleConstr (unqualify f)

> lookupTupleConstr :: Ident -> [ValueKind]
> lookupTupleConstr c = [tupleConstrs !! (tupleArity c - 2) | isTupleId c]

> tupleConstrs :: [ValueKind]
> tupleConstrs = map valueKind tupleDCs

\end{verbatim}
\paragraph{Operator precedences}
In order to parse infix expressions correctly, the compiler must know
the precedence and associativity of each operator. Operator
precedences are associated with entities and will be checked after
renaming. Nevertheless, we need to save precedences for ambiguous
names in order to handle them correctly while computing the exported
interface of a module.

If no fixity is assigned to an operator, it will be given the default
precedence 9 and assumed to be a left-associative operator.
\begin{verbatim}

> data OpPrec = OpPrec Infix Int deriving Eq

> instance Show OpPrec where
>   showsPrec _ (OpPrec fix p) = showString (assoc fix) . shows p
>     where assoc InfixL = "left "
>           assoc InfixR = "right "
>           assoc Infix  = "non-assoc "

> defaultP :: OpPrec
> defaultP = OpPrec InfixL 9

\end{verbatim}
The lookup functions for the environment, which maintains the operator
precedences, are simpler than for the type and value environments
because they do not need to handle tuple constructors.
\begin{verbatim}

> data PrecInfo = PrecInfo QualIdent OpPrec deriving (Eq,Show)

> instance Entity PrecInfo where
>   origName (PrecInfo op _) = op

> type PEnv = TopEnv PrecInfo

> bindP :: ModuleIdent -> Ident -> OpPrec -> PEnv -> PEnv
> bindP m op p = bindTopEnv m op (PrecInfo (qualifyWith m op) p)

> lookupP :: Ident -> PEnv -> [PrecInfo]
> lookupP = lookupTopEnv

> qualLookupP :: QualIdent -> PEnv -> [PrecInfo]
> qualLookupP = qualLookupTopEnv

\end{verbatim}
\paragraph{Evaluation modes}
The compiler collects the evaluation annotations for all functions in
an environment. As these annotations affect only declarations from the
current module, a flat environment mapping unqualified names onto
annotations is sufficient.
\begin{verbatim}

> type EvalEnv = Env Ident EvalAnnotation

> bindEval :: Ident -> EvalAnnotation -> EvalEnv -> EvalEnv
> bindEval = bindEnv

> lookupEval :: Ident -> EvalEnv -> Maybe EvalAnnotation
> lookupEval f evEnv = lookupEnv f evEnv

\end{verbatim}
\paragraph{Predefined types}
The unit and list data types must be predefined because the
declarations
\begin{verbatim}
data () = ()
data [] a = [] | a : [a]
\end{verbatim}
are not valid in Curry. The corresponding types
are available in the environments \texttt{initTCEnv} and
\texttt{initDCEnv}. In addition, the precedence of the infix list
constructor is available in the environment \texttt{initPEnv}.
\begin{verbatim}

> initPEnv :: PEnv
> initPEnv =
>   predefTopEnv qConsId (PrecInfo qConsId (OpPrec InfixR 5)) emptyTopEnv

> initTCEnv :: TCEnv
> initTCEnv = foldr (uncurry predefTC) emptyTopEnv predefTypes
>   where predefTC (TypeConstructor tc tys) cs =
>           predefTopEnv tc (DataType tc (length tys) (map (Just . fst) cs))

> initDCEnv :: ValueEnv
> initDCEnv =
>   foldr (uncurry predefDC) emptyTopEnv (concatMap snd predefTypes)
>   where predefDC c ty =
>           predefTopEnv c' (DataConstructor c' (constrType (polyType ty)))
>           where c' = qualify c
>         constrType (ForAll n ty) = ForAllExist n 0 ty

> predefTypes :: [(Type,[(Ident,Type)])]
> predefTypes =
>   let a = typeVar 0 in [
>     (unitType,   [(unitId,unitType)]),
>     (listType a, [(nilId,nilType a), (consId,consType a)])
>   ]
>   where nilType a = listType a
>         consType a = TypeArrow a (TypeArrow (listType a) (listType a))

\end{verbatim}
\paragraph{Free and bound variables}
The compiler needs to compute the sets of free and bound variables for
various entities. We will devote three type classes to that purpose.
The \texttt{QualExpr} class is expected to take into account that it
is possible to use a qualified name for referring to a function
defined in the current module and therefore \emph{M.x} and $x$, where
$M$ is the current module name, should be considered the same name.
However, note that this is correct only after renaming all local
definitions, as \emph{M.x} always denotes an entity defined at the
top-level.

The \texttt{Decl} instance of \texttt{QualExpr} returns all free
variables on the right hand side, regardless of whether they are bound
on the left hand side. This is more convenient because declarations are
usually processed in a declaration group where the set of free
variables cannot be computed independently for each declaration. Also
note that the operator in a unary minus expression is not a free
variable, but always refers to a global function from the prelude.
\begin{verbatim}

> class Expr e where
>   fv :: e -> [Ident]
> class QualExpr e where
>   qfv :: ModuleIdent -> e -> [Ident]
> class QuantExpr e where
>   bv :: e -> [Ident]

> instance Expr e => Expr [e] where
>   fv = concat . map fv
> instance QualExpr e => QualExpr [e] where
>   qfv m = concat . map (qfv m)
> instance QuantExpr e => QuantExpr [e] where
>   bv = concat . map bv

> instance QualExpr Decl where
>   qfv m (FunctionDecl _ _ eqs) = qfv m eqs
>   qfv m (PatternDecl _ _ rhs) = qfv m rhs
>   qfv _ _ = []

> instance QuantExpr Decl where
>   bv (FunctionDecl _ f _) = [f]
>   bv (ForeignDecl _ _ _ f _) = [f]
>   bv (PatternDecl _ t _) = bv t
>   bv (FreeDecl _ vs) = vs
>   bv _ = []

> instance QualExpr Equation where
>   qfv m (Equation _ lhs rhs) = filterBv lhs (qfv m rhs)

> instance QuantExpr Lhs where
>   bv = bv . snd . flatLhs

> instance QualExpr Rhs where
>   qfv m (SimpleRhs _ e ds) = filterBv ds (qfv m e ++ qfv m ds)
>   qfv m (GuardedRhs es ds) = filterBv ds (qfv m es ++ qfv m ds)

> instance QualExpr CondExpr where
>   qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

> instance QualExpr Expression where
>   qfv _ (Literal _) = []
>   qfv m (Variable v) = maybe [] return (localIdent m v)
>   qfv _ (Constructor _) = []
>   qfv m (Paren e) = qfv m e
>   qfv m (Typed e _) = qfv m e
>   qfv m (Tuple es) = qfv m es
>   qfv m (List es) = qfv m es
>   qfv m (ListCompr e qs) = foldr (qfvStmt m) (qfv m e) qs
>   qfv m (EnumFrom e) = qfv m e
>   qfv m (EnumFromThen e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromTo e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (UnaryMinus _ e) = qfv m e
>   qfv m (Apply e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (InfixApply e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
>   qfv m (LeftSection e op) = qfv m op ++ qfv m e
>   qfv m (RightSection op e) = qfv m op ++ qfv m e
>   qfv m (Lambda ts e) = filterBv ts (qfv m e)
>   qfv m (Let ds e) = filterBv ds (qfv m ds ++ qfv m e)
>   qfv m (Do sts e) = foldr (qfvStmt m) (qfv m e) sts
>   qfv m (IfThenElse e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (Case e alts) = qfv m e ++ qfv m alts

> qfvStmt :: ModuleIdent -> Statement -> [Ident] -> [Ident]
> qfvStmt m st fvs = qfv m st ++ filterBv st fvs

> instance QualExpr Statement where
>   qfv m (StmtExpr e) = qfv m e
>   qfv m (StmtDecl ds) = filterBv ds (qfv m ds)
>   qfv m (StmtBind t e) = qfv m e

> instance QualExpr Alt where
>   qfv m (Alt _ t rhs) = filterBv t (qfv m rhs)

> instance QuantExpr Statement where
>   bv (StmtExpr e) = []
>   bv (StmtBind t e) = bv t
>   bv (StmtDecl ds) = bv ds

> instance QualExpr InfixOp where
>   qfv m (InfixOp op) = qfv m (Variable op)
>   qfv _ (InfixConstr _) = []

> instance QuantExpr ConstrTerm where
>   bv (LiteralPattern _) = []
>   bv (NegativePattern _ _) = []
>   bv (VariablePattern v) = [v | v /= anonId]
>   bv (ConstructorPattern c ts) = bv ts
>   bv (InfixPattern t1 op t2) = bv t1 ++ bv t2
>   bv (ParenPattern t) = bv t
>   bv (TuplePattern ts) = bv ts
>   bv (ListPattern ts) = bv ts
>   bv (AsPattern v t) = v : bv t
>   bv (LazyPattern t) = bv t

> instance Expr TypeExpr where
>   fv (ConstructorType _ tys) = fv tys
>   fv (VariableType tv) = [tv]
>   fv (TupleType tys) = fv tys
>   fv (ListType ty) = fv ty
>   fv (ArrowType ty1 ty2) = fv ty1 ++ fv ty2

> filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
> filterBv e = filter (`notElemSet` fromListSet (bv e))

\end{verbatim}
\paragraph{Miscellany}
Error handling
\begin{verbatim}

> errorAt :: Monad m => Position -> String -> m a
> errorAt p msg = fail (atP p msg)

> internalError :: String -> a
> internalError what = error ("internal error: " ++ what)

\end{verbatim}
Name supply for the generation of (type) variable names.
\begin{verbatim}

> nameSupply :: [Ident]
> nameSupply = map mkIdent [c:showNum i | i <- [0..], c <- ['a'..'z']]
>   where showNum 0 = ""
>         showNum n = show n

\end{verbatim}
\ToDo{The \texttt{nameSupply} should respect the current case mode, 
i.e., use upper case for variables in Prolog mode.}

Here is a list of predicates identifying various kinds of
declarations.
\begin{verbatim}

> isTypeDecl :: TopDecl -> Bool
> isTypeDecl (DataDecl _ _ _ _) = True
> isTypeDecl (NewtypeDecl _ _ _ _) = True
> isTypeDecl (TypeDecl _ _ _ _) = True
> isTypeDecl (BlockDecl _) = False

> isInfixDecl, isTypeSig, isEvalAnnot :: Decl -> Bool
> isFreeDecl, isValueDecl :: Decl -> Bool
> isInfixDecl (InfixDecl _ _ _ _) = True
> isInfixDecl _ = False
> isTypeSig (TypeSig _ _ _) = True
> isTypeSig (ForeignDecl _ _ _ _ _) = True
> isTypeSig _ = False
> isEvalAnnot (EvalAnnot _ _ _) = True
> isEvalAnnot _ = False
> isFreeDecl (FreeDecl _ _) = True
> isFreeDecl _ = False
> isValueDecl (FunctionDecl _ _ _) = True
> isValueDecl (ForeignDecl _ _ _ _ _) = True
> isValueDecl (PatternDecl _ _ _) = True
> isValueDecl (FreeDecl _ _) = True
> isValueDecl _ = False

\end{verbatim}
The function \texttt{infixOp} converts an infix operator into an
expression.
\begin{verbatim}

> infixOp :: InfixOp -> Expression
> infixOp (InfixOp op) = Variable op
> infixOp (InfixConstr op) = Constructor op

\end{verbatim}
The function \texttt{linear} checks whether a list of entities is
linear, i.e., if every entity in the list occurs only once. If it is
non-linear, the first duplicate object is returned.
\begin{verbatim}

> data Linear a = Linear | NonLinear a

> linear :: Eq a => [a] -> Linear a
> linear (x:xs)
>   | x `elem` xs = NonLinear x
>   | otherwise = linear xs
> linear [] = Linear

\end{verbatim}
