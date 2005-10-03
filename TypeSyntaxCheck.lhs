% -*- LaTeX -*-
% $Id: TypeSyntaxCheck.lhs 1780 2005-10-03 18:54:07Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSyntaxCheck.lhs}
\section{Checking Type Definitions}
After the source file has been parsed and all modules have been
imported, the compiler first checks all type definitions and
signatures. In particular, this module disambiguates nullary
constructors and type variables, which -- in contrast to many other
declarative languages -- cannot be done in the parser due to the lack
of a capitalization convention.
\begin{verbatim}

> module TypeSyntaxCheck(typeSyntaxCheck,typeSyntaxCheckGoal) where
> import Base
> import Error
> import Monad
> import TopEnv

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment, which records all known type constructors.
The function \texttt{typeSyntaxCheck} first initializes this
environment from the imported type constructor environment. Next, the
all locally defined type constructors are inserted into the
environment, and, finally, the declarations are checked within this
environment. The final environment is returned in order to be used
later for checking the optional export list of the current module.
\begin{verbatim}

> typeSyntaxCheck :: ModuleIdent -> TCEnv -> [TopDecl]
>                 -> Error (TypeEnv,[TopDecl])
> typeSyntaxCheck m tcEnv ds =
>   case linear (map tconstr tds) of
>     Linear ->
>       do
>         ds' <- mapM (checkTopDecl env) ds
>         return (env,ds')
>     NonLinear (P p tc) -> errorAt p (duplicateType tc)
>   where tds = filter isTypeDecl ds
>         env = foldr (bindType m) (fmap typeKind tcEnv) tds

> typeSyntaxCheckGoal :: TCEnv -> Goal -> Error Goal
> typeSyntaxCheckGoal tcEnv (Goal p e ds) =
>   liftM2 (Goal p) (checkExpr env p e) (mapM (checkDecl env) ds)
>   where env = fmap typeKind tcEnv

> bindType :: ModuleIdent -> TopDecl -> TypeEnv -> TypeEnv
> bindType m (DataDecl _ tc _ cs) =
>   bindTop m tc (Data (qualifyWith m tc) (map constr cs))
> bindType m (NewtypeDecl _ tc _ nc) =
>   bindTop m tc (Data (qualifyWith m tc) [nconstr nc])
> bindType m (TypeDecl _ tc _ _) = bindTop m tc (Alias (qualifyWith m tc))
> bindType _ (BlockDecl _) = id

\end{verbatim}
The compiler allows anonymous type variables on the left hand side of
type declarations, but not on their right hand side. Function and
pattern declarations are traversed in order to check local type
signatures.
\begin{verbatim}

> checkTopDecl :: TypeEnv -> TopDecl -> Error TopDecl
> checkTopDecl env (DataDecl p tc tvs cs) =
>   do
>     checkTypeLhs env p tvs
>     liftM (DataDecl p tc tvs) (mapM (checkConstrDecl env tvs) cs)
> checkTopDecl env (NewtypeDecl p tc tvs nc) =
>   do
>     checkTypeLhs env p tvs
>     liftM (NewtypeDecl p tc tvs) (checkNewConstrDecl env tvs nc)
> checkTopDecl env (TypeDecl p tc tvs ty) =
>   do
>     checkTypeLhs env p tvs
>     liftM (TypeDecl p tc tvs) (checkClosedType env p tvs ty)
> checkTopDecl env (BlockDecl d) = liftM BlockDecl (checkDecl env d)

> checkDecl :: TypeEnv -> Decl -> Error Decl
> checkDecl env (TypeSig p vs ty) =
>   liftM (TypeSig p vs) (checkType env p ty)
> checkDecl env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (checkEquation env) eqs)
> checkDecl env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (checkRhs env rhs)
> checkDecl env (ForeignDecl p cc ie f ty) =
>   liftM (ForeignDecl p cc ie f) (checkType env p ty)
> checkDecl _ d = return d

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> Error ()
> checkTypeLhs env p tvs =
>   case filter isTypeConstr tvs of
>     [] ->
>       case linear (filter (anonId /=) tvs) of
>         Linear -> return ()
>         NonLinear tv -> errorAt p (nonLinear tv)
>     tv:_ -> errorAt p (noVariable tv)
>   where isTypeConstr tv = not (null (lookupType tv env))

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> Error ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   do
>     checkTypeLhs env p evs
>     liftM (ConstrDecl p evs c) (mapM (checkClosedType env p tvs') tys)
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   do
>     checkTypeLhs env p evs
>     liftM2 (flip (ConOpDecl p evs) op)
>            (checkClosedType env p tvs' ty1)
>            (checkClosedType env p tvs' ty2)
>   where tvs' = evs ++ tvs

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl
>                    -> Error NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p evs c ty) =
>   do
>     checkTypeLhs env p evs
>     liftM (NewConstrDecl p evs c) (checkClosedType env p tvs' ty)
>   where tvs' = evs ++ tvs

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: TypeEnv -> Equation -> Error Equation
> checkEquation env (Equation p lhs rhs) =
>   liftM (Equation p lhs) (checkRhs env rhs)

> checkRhs :: TypeEnv -> Rhs -> Error Rhs
> checkRhs env (SimpleRhs p e ds) =
>   liftM2 (SimpleRhs p) (checkExpr env p e) (mapM (checkDecl env) ds)
> checkRhs env (GuardedRhs es ds) =
>   liftM2 GuardedRhs (mapM (checkCondExpr env) es) (mapM (checkDecl env) ds)

> checkCondExpr :: TypeEnv -> CondExpr -> Error CondExpr
> checkCondExpr env (CondExpr p g e) =
>   liftM2 (CondExpr p) (checkExpr env p g) (checkExpr env p e)

> checkExpr :: TypeEnv -> Position -> Expression -> Error Expression
> checkExpr _ _ (Literal l) = return (Literal l)
> checkExpr _ _ (Variable v) = return (Variable v)
> checkExpr _ _ (Constructor c) = return (Constructor c)
> checkExpr env p (Paren e) = liftM Paren (checkExpr env p e)
> checkExpr env p (Typed e ty) =
>   liftM2 Typed (checkExpr env p e) (checkType env p ty)
> checkExpr env p (Tuple es) = liftM Tuple (mapM (checkExpr env p) es)
> checkExpr env p (List es) = liftM List (mapM (checkExpr env p) es)
> checkExpr env p (ListCompr e qs) =
>   liftM2 ListCompr (checkExpr env p e) (mapM (checkStmt env p) qs)
> checkExpr env p (EnumFrom e) = liftM EnumFrom (checkExpr env p e)
> checkExpr env p (EnumFromThen e1 e2) =
>   liftM2 EnumFromThen (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (EnumFromTo e1 e2) =
>   liftM2 EnumFromTo (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (EnumFromThenTo e1 e2 e3) =
>   liftM3 EnumFromThenTo
>          (checkExpr env p e1)
>          (checkExpr env p e2)
>          (checkExpr env p e3)
> checkExpr env p (UnaryMinus op e) = liftM (UnaryMinus op) (checkExpr env p e)
> checkExpr env p (Apply e1 e2) =
>   liftM2 Apply (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (InfixApply e1 op e2) =
>   liftM2 (flip InfixApply op) (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (LeftSection e op) =
>   liftM (flip LeftSection op) (checkExpr env p e)
> checkExpr env p (RightSection op e) =
>   liftM (RightSection op) (checkExpr env p e)
> checkExpr env p (Lambda ts e) = liftM (Lambda ts) (checkExpr env p e)
> checkExpr env p (Let ds e) =
>   liftM2 Let (mapM (checkDecl env) ds) (checkExpr env p e)
> checkExpr env p (Do sts e) =
>   liftM2 Do (mapM (checkStmt env p) sts) (checkExpr env p e)
> checkExpr env p (IfThenElse e1 e2 e3) =
>   liftM3 IfThenElse
>          (checkExpr env p e1)
>          (checkExpr env p e2)
>          (checkExpr env p e3)
> checkExpr env p (Case e alts) =
>   liftM2 Case (checkExpr env p e) (mapM (checkAlt env) alts)

> checkStmt :: TypeEnv -> Position -> Statement -> Error Statement
> checkStmt env p (StmtExpr e) = liftM StmtExpr (checkExpr env p e)
> checkStmt env p (StmtBind t e) = liftM (StmtBind t) (checkExpr env p e)
> checkStmt env p (StmtDecl ds) = liftM StmtDecl (mapM (checkDecl env) ds)

> checkAlt :: TypeEnv -> Alt -> Error Alt
> checkAlt env (Alt p t rhs) = liftM (Alt p t) (checkRhs env rhs)

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p ty
>     case filter (\tv -> tv == anonId || tv `notElem` tvs) (fv ty') of
>       [] -> return ty'
>       tv:_ -> errorAt p (unboundVariable tv)

> checkType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkType env p (ConstructorType tc tys) =
>   case qualLookupType tc env of
>     []
>       | not (isQualified tc) && null tys ->
>           return (VariableType (unqualify tc))
>       | otherwise -> errorAt p (undefinedType tc)
>     [_] -> liftM (ConstructorType tc) (mapM (checkType env p) tys)
>     _ -> errorAt p (ambiguousType tc)
> checkType env p (VariableType tv)
>   | tv == anonId = return (VariableType tv)
>   | otherwise = checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) =
>   liftM TupleType (mapM (checkType env p) tys)
> checkType env p (ListType ty) =
>   liftM ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   liftM2 ArrowType (checkType env p ty1) (checkType env p ty2)

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> tconstr :: TopDecl -> P Ident
> tconstr (DataDecl p tc _ _) = P p tc
> tconstr (NewtypeDecl p tc _ _) = P p tc
> tconstr (TypeDecl p tc _ _) = P p tc
> tconstr (BlockDecl _) = internalError "tconstr"

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type " ++ qualName tc

> ambiguousType :: QualIdent -> String
> ambiguousType tc = "Ambiguous type " ++ qualName tc

> duplicateType :: Ident -> String
> duplicateType tc = "More than one definition for type " ++ name tc

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noVariable :: Ident -> String
> noVariable tv =
>   "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> unboundVariable :: Ident -> String
> unboundVariable tv = "Unbound type variable " ++ name tv

\end{verbatim}
