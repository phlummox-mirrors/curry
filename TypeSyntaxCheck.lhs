% -*- LaTeX -*-
% $Id: TypeSyntaxCheck.lhs 1774 2005-09-23 08:00:01Z wlux $
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
of a capitalization convention. In addition, this module checks that
all type constructors and type variables are unambiguously defined and
no type constructor is defined more than once.

Since Curry currently does not support type classes, all types must be
of first order kind ($\star$). This makes kind checking in Curry
rather trivial; the compiler must only ensure that all type
constructor applications are saturated. Because this check is so
simple it is performed in this module, too.
\begin{verbatim}

> module TypeSyntaxCheck(typeSyntaxCheck,typeSyntaxCheckGoal) where
> import Base
> import TopEnv

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment mapping all type constructors onto their
arity. The function \texttt{typeSyntaxCheck} first initializes this
environment by filtering out the arity of each type constructor from
the imported type environment. Next, the arities of all locally
defined type constructors are inserted into the environment, and,
finally, the declarations are checked within this environment.
\begin{verbatim}

> typeSyntaxCheck :: ModuleIdent -> TCEnv -> [TopDecl] -> (TypeEnv,[TopDecl])
> typeSyntaxCheck m tcEnv ds =
>   case linear (map tconstr ds') of
>     Linear -> (env,map (checkTopDecl env) ds)
>     NonLinear (P p tc) -> errorAt p (duplicateType tc)
>   where ds' = filter isTypeDecl ds
>         env = foldr (bindType m) (fmap typeKind tcEnv) ds'

> typeSyntaxCheckGoal :: TCEnv -> Goal -> Goal
> typeSyntaxCheckGoal tcEnv (Goal p e ds) =
>   Goal p (checkExpr env p e) (map (checkDecl env) ds)
>   where env = fmap typeKind tcEnv

> bindType :: ModuleIdent -> TopDecl -> TypeEnv -> TypeEnv
> bindType m (DataDecl _ tc tvs cs) =
>   bindTop m tc (typeCon Data m tc tvs (map constr cs))
> bindType m (NewtypeDecl _ tc tvs nc) =
>   bindTop m tc (typeCon Data m tc tvs [nconstr nc])
> bindType m (TypeDecl _ tc tvs _) = bindTop m tc (typeCon Alias m tc tvs)
> bindType _ (BlockDecl _) = id

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> Ident -> [Ident] -> a
> typeCon f m tc tvs = f (qualifyWith m tc) (length tvs)

\end{verbatim}
The compiler allows anonymous type variables on the left hand side of
type declarations, but not on their right hand side. Function and
pattern declarations are traversed in order to check local type
signatures.
\begin{verbatim}

> checkTopDecl :: TypeEnv -> TopDecl -> TopDecl
> checkTopDecl env (DataDecl p tc tvs cs) =
>   DataDecl p tc tvs' (map (checkConstrDecl env tvs') cs)
>   where tvs' = checkTypeLhs env p tvs
> checkTopDecl env (NewtypeDecl p tc tvs nc) =
>   NewtypeDecl p tc tvs' (checkNewConstrDecl env tvs' nc)
>   where tvs' = checkTypeLhs env p tvs
> checkTopDecl env (TypeDecl p tc tvs ty) =
>   TypeDecl p tc tvs' (checkClosedType env p tvs' ty)
>   where tvs' = checkTypeLhs env p tvs
> checkTopDecl env (BlockDecl d) = BlockDecl (checkDecl env d)

> checkDecl :: TypeEnv -> Decl -> Decl
> checkDecl env (TypeSig p vs ty) =
>   TypeSig p vs (checkType env p ty)
> checkDecl env (FunctionDecl p f eqs) =
>   FunctionDecl p f (map (checkEquation env) eqs)
> checkDecl env (PatternDecl p t rhs) =
>   PatternDecl p t (checkRhs env rhs)
> checkDecl env (ForeignDecl p cc ie f ty) =
>   ForeignDecl p cc ie f (checkType env p ty)
> checkDecl _ d = d

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> [Ident]
> checkTypeLhs env p (tv:tvs)
>   | tv == anonId = tv : checkTypeLhs env p tvs
>   | isTypeConstr tv = errorAt p (noVariable tv)
>   | tv `elem` tvs = errorAt p (nonLinear tv)
>   | otherwise = tv : checkTypeLhs env p tvs
>   where isTypeConstr tv = not (null (lookupType tv env))
> checkTypeLhs _ _ [] = []

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs' c (map (checkClosedType env p tvs') tys)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs' (checkClosedType env p tvs' ty1) op
>             (checkClosedType env p tvs' ty2)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl -> NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs' c (checkClosedType env p tvs' ty)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: TypeEnv -> Equation -> Equation
> checkEquation env (Equation p lhs rhs) = Equation p lhs (checkRhs env rhs)

> checkRhs :: TypeEnv -> Rhs -> Rhs
> checkRhs env (SimpleRhs p e ds) =
>   SimpleRhs p (checkExpr env p e) (map (checkDecl env) ds)
> checkRhs env (GuardedRhs es ds) =
>   GuardedRhs (map (checkCondExpr env) es) (map (checkDecl env) ds)

> checkCondExpr :: TypeEnv -> CondExpr -> CondExpr
> checkCondExpr env (CondExpr p g e) =
>   CondExpr p (checkExpr env p g) (checkExpr env p e)

> checkExpr :: TypeEnv -> Position -> Expression -> Expression
> checkExpr _ _ (Literal l) = Literal l
> checkExpr _ _ (Variable v) = Variable v
> checkExpr _ _ (Constructor c) = Constructor c
> checkExpr env p (Paren e) = Paren (checkExpr env p e)
> checkExpr env p (Typed e ty) =
>   Typed (checkExpr env p e) (checkType env p ty)
> checkExpr env p (Tuple es) = Tuple (map (checkExpr env p) es)
> checkExpr env p (List es) = List (map (checkExpr env p) es)
> checkExpr env p (ListCompr e qs) =
>   ListCompr (checkExpr env p e) (map (checkStmt env p) qs)
> checkExpr env p (EnumFrom e) = EnumFrom (checkExpr env p e)
> checkExpr env p (EnumFromThen e1 e2) =
>   EnumFromThen (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (EnumFromTo e1 e2) =
>   EnumFromTo (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (EnumFromThenTo e1 e2 e3) =
>   EnumFromThenTo (checkExpr env p e1) (checkExpr env p e2)
>                  (checkExpr env p e3)
> checkExpr env p (UnaryMinus op e) = UnaryMinus op (checkExpr env p e)
> checkExpr env p (Apply e1 e2) =
>   Apply (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (InfixApply e1 op e2) =
>   InfixApply (checkExpr env p e1) op (checkExpr env p e2)
> checkExpr env p (LeftSection e op) = LeftSection (checkExpr env p e) op
> checkExpr env p (RightSection op e) = RightSection op (checkExpr env p e)
> checkExpr env p (Lambda ts e) = Lambda ts (checkExpr env p e)
> checkExpr env p (Let ds e) =
>   Let (map (checkDecl env) ds) (checkExpr env p e)
> checkExpr env p (Do sts e) =
>   Do (map (checkStmt env p) sts) (checkExpr env p e)
> checkExpr env p (IfThenElse e1 e2 e3) =
>   IfThenElse (checkExpr env p e1) (checkExpr env p e2)
>              (checkExpr env p e3)
> checkExpr env p (Case e alts) =
>   Case (checkExpr env p e) (map (checkAlt env) alts)

> checkStmt :: TypeEnv -> Position -> Statement -> Statement
> checkStmt env p (StmtExpr e) = StmtExpr (checkExpr env p e)
> checkStmt env p (StmtBind t e) = StmtBind t (checkExpr env p e)
> checkStmt env p (StmtDecl ds) = StmtDecl (map (checkDecl env) ds)

> checkAlt :: TypeEnv -> Alt -> Alt
> checkAlt env (Alt p t rhs) = Alt p t (checkRhs env rhs)

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosedType env p tvs ty = checkClosed p tvs (checkType env p ty)

> checkType :: TypeEnv -> Position -> TypeExpr -> TypeExpr
> checkType env p (ConstructorType tc tys) =
>   case qualLookupType tc env of
>     []
>       | not (isQualified tc) && null tys -> VariableType (unqualify tc)
>       | otherwise -> errorAt p (undefinedType tc)
>     [t]
>       | n == n' -> ConstructorType tc (map (checkType env p) tys)
>       | otherwise -> errorAt p (wrongArity tc n n')
>       where n = arity t
>             n' = length tys
>     _ -> errorAt p (ambiguousType tc)
> checkType env p (VariableType tv)
>   | tv == anonId = VariableType tv
>   | otherwise = checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) =
>   TupleType (map (checkType env p) tys)
> checkType env p (ListType ty) =
>   ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   ArrowType (checkType env p ty1) (checkType env p ty2)

> checkClosed :: Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosed p tvs (ConstructorType tc tys) =
>   ConstructorType tc (map (checkClosed p tvs) tys)
> checkClosed p tvs (VariableType tv)
>   | tv == anonId || tv `notElem` tvs = errorAt p (unboundVariable tv)
>   | otherwise = VariableType tv
> checkClosed p tvs (TupleType tys) =
>   TupleType (map (checkClosed p tvs) tys)
> checkClosed p tvs (ListType ty) =
>   ListType (checkClosed p tvs ty)
> checkClosed p tvs (ArrowType ty1 ty2) =
>   ArrowType (checkClosed p tvs ty1) (checkClosed p tvs ty2)

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> tconstr :: TopDecl -> P Ident
> tconstr (DataDecl p tc _ _) = P p tc
> tconstr (NewtypeDecl p tc _ _) = P p tc
> tconstr (TypeDecl p tc _ _) = P p tc
> tconstr (BlockDecl _) = internalError "tconstr"

> arity :: TypeKind -> Int
> arity (Data _ n _) = n
> arity (Alias _ n) = n

\end{verbatim}
Error messages:
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

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity tc arity argc =
>   "Type constructor " ++ qualName tc ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> unboundVariable :: Ident -> String
> unboundVariable tv = "Unbound type variable " ++ name tv

\end{verbatim}
