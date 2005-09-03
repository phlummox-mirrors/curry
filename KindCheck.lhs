% -*- LaTeX -*-
% $Id: KindCheck.lhs 1758 2005-09-03 10:06:41Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{KindCheck.lhs}
\section{Checking Type Definitions}
After the source file has been parsed and all modules have been
imported, the compiler first performs kind checking on all type
definitions and signatures. Because Curry currently does not support
type classes, kind checking is rather trivial. All types must be of
first order kind ($\star$), i.e., all type constructor applications
must be saturated.

During kind checking, this module will also disambiguate nullary
constructors and type variables which -- in contrast to Haskell -- is
not possible on purely syntactic criteria. In addition it is checked
that all type constructors and type variables occurring on the right
hand side of a type declaration are actually defined and no identifier
is defined more than once.
\begin{verbatim}

> module KindCheck(kindCheck,kindCheckGoal) where
> import Base
> import Maybe
> import TopEnv

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment containing the kind information for all type
constructors. The function \texttt{kindCheck} first initializes this
environment by filtering out the arity of each type constructor from
the imported type environment. Next, the arities of all locally
defined type constructors are inserted into the environment, and,
finally, the declarations are checked within this environment.
\begin{verbatim}

> kindCheck :: ModuleIdent -> TCEnv -> [TopDecl] -> [TopDecl]
> kindCheck m tcEnv ds =
>   case linear (map tconstr ds') of
>     Linear -> map (checkTopDecl kEnv) ds
>     NonLinear (PIdent p tc) -> errorAt p (duplicateType tc)
>   where ds' = filter isTypeDecl ds
>         kEnv = foldr (bindArity m) (fmap tcArity tcEnv) ds'

> kindCheckGoal :: TCEnv -> Goal -> Goal
> kindCheckGoal tcEnv (Goal p e ds) =
>   Goal p (checkExpr kEnv p e) (map (checkDecl kEnv) ds)
>   where kEnv = fmap tcArity tcEnv

\end{verbatim}
The kind environment only needs to record the arity of each type constructor.
\begin{verbatim}

> type KindEnv = TopEnv Int

> bindArity :: ModuleIdent -> TopDecl -> KindEnv -> KindEnv
> bindArity m (DataDecl p tc tvs _) = bindArity' m p tc tvs
> bindArity m (NewtypeDecl p tc tvs _) = bindArity' m p tc tvs
> bindArity m (TypeDecl p tc tvs _) = bindArity' m p tc tvs
> bindArity _ (BlockDecl _) = id

> bindArity' :: ModuleIdent -> Position -> Ident -> [Ident]
>            -> KindEnv -> KindEnv
> bindArity' m p tc tvs = bindTopEnv tc n . qualBindTopEnv (qualifyWith m tc) n
>   where n = length tvs

> lookupKind :: Ident -> KindEnv -> [Int]
> lookupKind = lookupTopEnv

> qualLookupKind :: QualIdent -> KindEnv -> [Int]
> qualLookupKind = qualLookupTopEnv

\end{verbatim}
When type declarations are checked, the compiler will allow anonymous
type variables on the left hand side of the declaration, but not on
the right hand side. Function and pattern declarations must be
traversed because they can contain local type signatures.
\begin{verbatim}

> checkTopDecl :: KindEnv -> TopDecl -> TopDecl
> checkTopDecl kEnv (DataDecl p tc tvs cs) =
>   DataDecl p tc tvs' (map (checkConstrDecl kEnv tvs') cs)
>   where tvs' = checkTypeLhs kEnv p tvs
> checkTopDecl kEnv (NewtypeDecl p tc tvs nc) =
>   NewtypeDecl p tc tvs' (checkNewConstrDecl kEnv tvs' nc)
>   where tvs' = checkTypeLhs kEnv p tvs
> checkTopDecl kEnv (TypeDecl p tc tvs ty) =
>   TypeDecl p tc tvs' (checkClosedType kEnv p tvs' ty)
>   where tvs' = checkTypeLhs kEnv p tvs
> checkTopDecl kEnv (BlockDecl d) = BlockDecl (checkDecl kEnv d)

> checkDecl :: KindEnv -> Decl -> Decl
> checkDecl kEnv (TypeSig p vs ty) =
>   TypeSig p vs (checkType kEnv p ty)
> checkDecl kEnv (FunctionDecl p f eqs) =
>   FunctionDecl p f (map (checkEquation kEnv) eqs)
> checkDecl kEnv (PatternDecl p t rhs) =
>   PatternDecl p t (checkRhs kEnv rhs)
> checkDecl kEnv (ForeignDecl p cc ie f ty) =
>   ForeignDecl p cc ie f (checkType kEnv p ty)
> checkDecl _ d = d

> checkTypeLhs :: KindEnv -> Position -> [Ident] -> [Ident]
> checkTypeLhs kEnv p (tv:tvs)
>   | tv == anonId = tv : checkTypeLhs kEnv p tvs
>   | isTypeConstr tv = errorAt p (noVariable tv)
>   | tv `elem` tvs = errorAt p (nonLinear tv)
>   | otherwise = tv : checkTypeLhs kEnv p tvs
>   where isTypeConstr tv = not (null (lookupKind tv kEnv))
> checkTypeLhs kEnv p [] = []

> checkConstrDecl :: KindEnv -> [Ident] -> ConstrDecl -> ConstrDecl
> checkConstrDecl kEnv tvs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs' c (map (checkClosedType kEnv p tvs') tys)
>   where evs' = checkTypeLhs kEnv p evs
>         tvs' = evs' ++ tvs
> checkConstrDecl kEnv tvs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs' (checkClosedType kEnv p tvs' ty1) op
>             (checkClosedType kEnv p tvs' ty2)
>   where evs' = checkTypeLhs kEnv p evs
>         tvs' = evs' ++ tvs

> checkNewConstrDecl :: KindEnv -> [Ident] -> NewConstrDecl -> NewConstrDecl
> checkNewConstrDecl kEnv tvs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs' c (checkClosedType kEnv p tvs' ty)
>   where evs' = checkTypeLhs kEnv p evs
>         tvs' = evs' ++ tvs

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: KindEnv -> Equation -> Equation
> checkEquation kEnv (Equation p lhs rhs) = Equation p lhs (checkRhs kEnv rhs)

> checkRhs :: KindEnv -> Rhs -> Rhs
> checkRhs kEnv (SimpleRhs p e ds) =
>   SimpleRhs p (checkExpr kEnv p e) (map (checkDecl kEnv) ds)
> checkRhs kEnv (GuardedRhs es ds) =
>   GuardedRhs (map (checkCondExpr kEnv) es) (map (checkDecl kEnv) ds)

> checkCondExpr :: KindEnv -> CondExpr -> CondExpr
> checkCondExpr kEnv (CondExpr p g e) =
>   CondExpr p (checkExpr kEnv p g) (checkExpr kEnv p e)

> checkExpr :: KindEnv -> Position -> Expression -> Expression
> checkExpr _ _ (Literal l) = Literal l
> checkExpr _ _ (Variable v) = Variable v
> checkExpr _ _ (Constructor c) = Constructor c
> checkExpr kEnv p (Paren e) = Paren (checkExpr kEnv p e)
> checkExpr kEnv p (Typed e ty) =
>   Typed (checkExpr kEnv p e) (checkType kEnv p ty)
> checkExpr kEnv p (Tuple es) = Tuple (map (checkExpr kEnv p) es)
> checkExpr kEnv p (List es) = List (map (checkExpr kEnv p) es)
> checkExpr kEnv p (ListCompr e qs) =
>   ListCompr (checkExpr kEnv p e) (map (checkStmt kEnv p) qs)
> checkExpr kEnv p (EnumFrom e) = EnumFrom (checkExpr kEnv p e)
> checkExpr kEnv p (EnumFromThen e1 e2) =
>   EnumFromThen (checkExpr kEnv p e1) (checkExpr kEnv p e2)
> checkExpr kEnv p (EnumFromTo e1 e2) =
>   EnumFromTo (checkExpr kEnv p e1) (checkExpr kEnv p e2)
> checkExpr kEnv p (EnumFromThenTo e1 e2 e3) =
>   EnumFromThenTo (checkExpr kEnv p e1) (checkExpr kEnv p e2)
>                  (checkExpr kEnv p e3)
> checkExpr kEnv p (UnaryMinus op e) = UnaryMinus op (checkExpr kEnv p e)
> checkExpr kEnv p (Apply e1 e2) =
>   Apply (checkExpr kEnv p e1) (checkExpr kEnv p e2)
> checkExpr kEnv p (InfixApply e1 op e2) =
>   InfixApply (checkExpr kEnv p e1) op (checkExpr kEnv p e2)
> checkExpr kEnv p (LeftSection e op) = LeftSection (checkExpr kEnv p e) op
> checkExpr kEnv p (RightSection op e) = RightSection op (checkExpr kEnv p e)
> checkExpr kEnv p (Lambda ts e) = Lambda ts (checkExpr kEnv p e)
> checkExpr kEnv p (Let ds e) =
>   Let (map (checkDecl kEnv) ds) (checkExpr kEnv p e)
> checkExpr kEnv p (Do sts e) =
>   Do (map (checkStmt kEnv p) sts) (checkExpr kEnv p e)
> checkExpr kEnv p (IfThenElse e1 e2 e3) =
>   IfThenElse (checkExpr kEnv p e1) (checkExpr kEnv p e2)
>              (checkExpr kEnv p e3)
> checkExpr kEnv p (Case e alts) =
>   Case (checkExpr kEnv p e) (map (checkAlt kEnv) alts)

> checkStmt :: KindEnv -> Position -> Statement -> Statement
> checkStmt kEnv p (StmtExpr e) = StmtExpr (checkExpr kEnv p e)
> checkStmt kEnv p (StmtBind t e) = StmtBind t (checkExpr kEnv p e)
> checkStmt kEnv p (StmtDecl ds) = StmtDecl (map (checkDecl kEnv) ds)

> checkAlt :: KindEnv -> Alt -> Alt
> checkAlt kEnv (Alt p t rhs) = Alt p t (checkRhs kEnv rhs)

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: KindEnv -> Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosedType kEnv p tvs ty = checkClosed p tvs (checkType kEnv p ty)

> checkType :: KindEnv -> Position -> TypeExpr -> TypeExpr
> checkType kEnv p (ConstructorType tc tys) =
>   case qualLookupKind tc kEnv of
>     []
>       | not (isQualified tc) && null tys -> VariableType (unqualify tc)
>       | otherwise -> errorAt p (undefinedType tc)
>     [n]
>       | n == n' -> ConstructorType tc (map (checkType kEnv p) tys)
>       | otherwise -> errorAt p (wrongArity tc n n')
>       where n' = length tys
>     _ -> errorAt p (ambiguousType tc)
> checkType kEnv p (VariableType tv)
>   | tv == anonId = VariableType tv
>   | otherwise = checkType kEnv p (ConstructorType (qualify tv) [])
> checkType kEnv p (TupleType tys) =
>   TupleType (map (checkType kEnv p) tys)
> checkType kEnv p (ListType ty) =
>   ListType (checkType kEnv p ty)
> checkType kEnv p (ArrowType ty1 ty2) =
>   ArrowType (checkType kEnv p ty1) (checkType kEnv p ty2)

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
Auxiliary definitions
\begin{verbatim}

> tconstr :: TopDecl -> PIdent
> tconstr (DataDecl p tc _ _) = PIdent p tc
> tconstr (NewtypeDecl p tc _ _) = PIdent p tc
> tconstr (TypeDecl p tc _ _) = PIdent p tc
> tconstr (BlockDecl _) = internalError "tconstr"

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
