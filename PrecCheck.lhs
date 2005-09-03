% -*- LaTeX -*-
% $Id: PrecCheck.lhs 1758 2005-09-03 10:06:41Z wlux $
%
% Copyright (c) 2001-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PrecCheck.lhs}
\section{Checking Precedences of Infix Operators}
The parser does not know the relative precedences of infix operators
and therefore parses them as if they all associate to the right and
have the same precedence. After syntax checking, the compiler is going
to check all infix applications in the module and rearrange them
according to the relative precedences of the operators involved.
\begin{verbatim}

> module PrecCheck(precCheck,precCheckGoal) where
> import Base
> import List

\end{verbatim}
For each declaration group, the compiler extends the precedence
environment using the fixity declarations from that scope. As a minor
optimization, we ignore all fixity declarations that assign the
default precedence to an operator.
\begin{verbatim}

> bindPrecs :: ModuleIdent -> [Decl] -> PEnv -> PEnv
> bindPrecs m ds pEnv = foldr bindPrec pEnv ds
>   where bindPrec (InfixDecl _ fix pr ops) pEnv
>           | p == defaultP = pEnv
>           | otherwise = foldr (flip (bindP m) p) pEnv ops
>           where p = OpPrec fix pr
>         bindPrec _ pEnv = pEnv

\end{verbatim}
With the help of the precedence environment, the compiler checks all
infix applications and sections in the program. This pass will modify
the parse tree such that for nested infix applications the operator
with the lowest precedence becomes the root and that two adjacent
operators with the same precedence will not have conflicting
associativities. The top-level precedence environment is returned
because it is used for constructing the module's interface.
\begin{verbatim}

> precCheck :: ModuleIdent -> PEnv -> [TopDecl] -> (PEnv,[TopDecl])
> precCheck m pEnv ds = (pEnv',ds')
>   where pEnv' = bindPrecs m [d | BlockDecl d <- ds] pEnv
>         ds' = map (checkTopDecl m pEnv') ds

> precCheckGoal :: PEnv -> Goal -> Goal
> precCheckGoal pEnv (Goal p e ds) = Goal p (checkExpr m p pEnv' e) ds'
>   where (pEnv',ds') = checkDecls m pEnv ds
>         m = emptyMIdent

> checkDecls :: ModuleIdent -> PEnv -> [Decl] -> (PEnv,[Decl])
> checkDecls m pEnv ds = pEnv' `seq` (pEnv',ds')
>   where pEnv' = bindPrecs m ds pEnv
>         ds' = map (checkDecl m pEnv') ds

> checkTopDecl :: ModuleIdent -> PEnv -> TopDecl -> TopDecl
> checkTopDecl m pEnv (BlockDecl d) = BlockDecl (checkDecl m pEnv d)
> checkTopDecl _ _ d = d

> checkDecl :: ModuleIdent -> PEnv -> Decl -> Decl
> checkDecl m pEnv (FunctionDecl p f eqs) =
>   FunctionDecl p f (map (checkEqn m pEnv) eqs)
> checkDecl m pEnv (PatternDecl p t rhs) =
>   PatternDecl p (checkConstrTerm p pEnv t) (checkRhs m pEnv rhs)
> checkDecl _ _ d = d

> checkEqn :: ModuleIdent -> PEnv -> Equation -> Equation
> checkEqn m pEnv (Equation p lhs rhs) =
>   Equation p (checkLhs p pEnv lhs) (checkRhs m pEnv rhs)

> checkLhs :: Position -> PEnv -> Lhs -> Lhs
> checkLhs p pEnv (FunLhs f ts) = FunLhs f (map (checkConstrTerm p pEnv) ts)
> checkLhs p pEnv (OpLhs t1 op t2) = t1' `seq` t2' `seq` OpLhs t1' op t2'
>   where t1' = checkOpL p pEnv op (checkConstrTerm p pEnv t1)
>         t2' = checkOpR p pEnv op (checkConstrTerm p pEnv t2)
> checkLhs p pEnv (ApLhs lhs ts) =
>   ApLhs (checkLhs p pEnv lhs) (map (checkConstrTerm p pEnv) ts)

> checkConstrTerm :: Position -> PEnv -> ConstrTerm -> ConstrTerm
> checkConstrTerm _ _ (LiteralPattern l) = LiteralPattern l
> checkConstrTerm _ _ (NegativePattern op l) = NegativePattern op l
> checkConstrTerm _ _ (VariablePattern v) = VariablePattern v
> checkConstrTerm p pEnv (ConstructorPattern c ts) =
>   ConstructorPattern c (map (checkConstrTerm p pEnv) ts)
> checkConstrTerm p pEnv (InfixPattern t1 op t2) =
>   fixPrecT p pEnv (checkConstrTerm p pEnv t1) op (checkConstrTerm p pEnv t2)
> checkConstrTerm p pEnv (ParenPattern t) =
>   ParenPattern (checkConstrTerm p pEnv t)
> checkConstrTerm p pEnv (TuplePattern ts) =
>   TuplePattern (map (checkConstrTerm p pEnv) ts)
> checkConstrTerm p pEnv (ListPattern ts) =
>   ListPattern (map (checkConstrTerm p pEnv) ts)
> checkConstrTerm p pEnv (AsPattern v t) =
>   AsPattern v (checkConstrTerm p pEnv t)
> checkConstrTerm p pEnv (LazyPattern t) =
>   LazyPattern (checkConstrTerm p pEnv t)

> checkRhs :: ModuleIdent -> PEnv -> Rhs -> Rhs
> checkRhs m pEnv (SimpleRhs p e ds) = SimpleRhs p (checkExpr m p pEnv' e) ds'
>   where (pEnv',ds') = checkDecls m pEnv ds
> checkRhs m pEnv (GuardedRhs es ds) =
>   GuardedRhs (map (checkCondExpr m pEnv') es) ds'
>   where (pEnv',ds') = checkDecls m pEnv ds

> checkCondExpr :: ModuleIdent -> PEnv -> CondExpr -> CondExpr
> checkCondExpr m pEnv (CondExpr p g e) =
>   CondExpr p (checkExpr m p pEnv g) (checkExpr m p pEnv e)

> checkExpr :: ModuleIdent -> Position -> PEnv -> Expression -> Expression
> checkExpr _ _ _ (Literal l) = Literal l
> checkExpr _ _ _ (Variable v) = Variable v
> checkExpr _ _ _ (Constructor c) = Constructor c
> checkExpr m p pEnv (Paren e) = Paren (checkExpr m p pEnv e)
> checkExpr m p pEnv (Typed e ty) = Typed (checkExpr m p pEnv e) ty
> checkExpr m p pEnv (Tuple es) = Tuple (map (checkExpr m p pEnv) es)
> checkExpr m p pEnv (List es) = List (map (checkExpr m p pEnv) es)
> checkExpr m p pEnv (ListCompr e qs) = ListCompr (checkExpr m p pEnv' e) qs'
>   where (pEnv',qs') = mapAccumL (checkStmt m p) pEnv qs
> checkExpr m p pEnv (EnumFrom e) = EnumFrom (checkExpr m p pEnv e)
> checkExpr m p pEnv (EnumFromThen e1 e2) =
>   EnumFromThen (checkExpr m p pEnv e1) (checkExpr m p pEnv e2)
> checkExpr m p pEnv (EnumFromTo e1 e2) =
>   EnumFromTo (checkExpr m p pEnv e1) (checkExpr m p pEnv e2)
> checkExpr m p pEnv (EnumFromThenTo e1 e2 e3) =
>   EnumFromThenTo (checkExpr m p pEnv e1)
>                  (checkExpr m p pEnv e2)
>                  (checkExpr m p pEnv e3)
> checkExpr m p pEnv (UnaryMinus op e) = UnaryMinus op (checkExpr m p pEnv e)
> checkExpr m p pEnv (Apply e1 e2) =
>   Apply (checkExpr m p pEnv e1) (checkExpr m p pEnv e2)
> checkExpr m p pEnv (InfixApply e1 op e2) =
>   fixPrec p pEnv (checkExpr m p pEnv e1) op (checkExpr m p pEnv e2)
> checkExpr m p pEnv (LeftSection e op) =
>   checkLSection p pEnv op (checkExpr m p pEnv e)
> checkExpr m p pEnv (RightSection op e) =
>   checkRSection p pEnv op (checkExpr m p pEnv e)
> checkExpr m p pEnv (Lambda ts e) =
>   Lambda (map (checkConstrTerm p pEnv) ts) (checkExpr m p pEnv e)
> checkExpr m p pEnv (Let ds e) = Let ds' (checkExpr m p pEnv' e)
>   where (pEnv',ds') = checkDecls m pEnv ds
> checkExpr m p pEnv (Do sts e) = Do sts' (checkExpr m p pEnv' e)
>   where (pEnv',sts') = mapAccumL (checkStmt m p) pEnv sts
> checkExpr m p pEnv (IfThenElse e1 e2 e3) =
>   IfThenElse (checkExpr m p pEnv e1)
>              (checkExpr m p pEnv e2)
>              (checkExpr m p pEnv e3)
> checkExpr m p pEnv (Case e alts) =
>   Case (checkExpr m p pEnv e) (map (checkAlt m pEnv) alts)

> checkStmt :: ModuleIdent -> Position -> PEnv -> Statement -> (PEnv,Statement)
> checkStmt m p pEnv (StmtExpr e) = (pEnv,StmtExpr (checkExpr m p pEnv e))
> checkStmt m _ pEnv (StmtDecl ds) = pEnv' `seq` (pEnv',StmtDecl ds')
>   where (pEnv',ds') = checkDecls m pEnv ds
> checkStmt m p pEnv (StmtBind t e) =
>   (pEnv,StmtBind (checkConstrTerm p pEnv t) (checkExpr m p pEnv e))

> checkAlt :: ModuleIdent -> PEnv -> Alt -> Alt
> checkAlt m pEnv (Alt p t rhs) =
>   Alt p (checkConstrTerm p pEnv t) (checkRhs m pEnv rhs)

\end{verbatim}
The functions \texttt{fixPrec}, \texttt{fixUPrec}, and
\texttt{fixRPrec} check the relative precedences of adjacent infix
operators in nested infix applications and unary negations. The
expressions will be reordered such that the infix operator with the
lowest precedence becomes the root of the expression. \emph{The
functions rely on the fact that the parser constructs infix
applications in a right-associative fashion}, i.e., the left
argument of an infix application is never an infix application. In
addition, a unary negation never has an infix application as its
argument.

The function \texttt{fixPrec} checks whether the left argument of an
infix application is a unary negation and eventually reorders the
expression if the precedence of the infix operator is higher than that
of unary negation. This is done with the help of the function
\texttt{fixUPrec}. In any case, the function \texttt{fixRPrec} is used
for fixing the precedence of the infix operator and that of its right
argument. Note that both arguments already have been checked before
\texttt{fixPrec} is called.
\begin{verbatim}

> fixPrec :: Position -> PEnv -> Expression -> InfixOp -> Expression
>         -> Expression
> fixPrec p pEnv (UnaryMinus uop e1) op e2
>   | pr < 6 || pr == 6 && fix == InfixL =
>       fixRPrec p pEnv (UnaryMinus uop e1) op e2
>   | pr > 6 = fixUPrec p pEnv uop e1 op e2
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op)
>   where OpPrec fix pr = opPrec op pEnv
> fixPrec p pEnv e1 op e2 = fixRPrec p pEnv e1 op e2

> fixUPrec :: Position -> PEnv -> Ident -> Expression -> InfixOp -> Expression
>          -> Expression
> fixUPrec p pEnv uop  _ op (UnaryMinus _ _) =
>   errorAt p $ ambiguousParse "operator" (opName op) (qualify uop)
> fixUPrec p pEnv uop e1 op1 (InfixApply e2 op2 e3)
>   | pr2 < 6 || pr2 == 6 && fix2 == InfixL =
>       InfixApply (fixUPrec p pEnv uop e1 op1 e2) op2 e3
>   | pr2 > 6 = UnaryMinus uop (fixRPrec p pEnv e1 op1 (InfixApply e2 op2 e3))
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> fixUPrec _ _ uop e1 op e2 = UnaryMinus uop (InfixApply e1 op e2)

> fixRPrec :: Position -> PEnv -> Expression -> InfixOp -> Expression
>          -> Expression
> fixRPrec p pEnv e1 op (UnaryMinus uop e2)
>   | pr < 6 = InfixApply e1 op (UnaryMinus uop e2)
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op) (qualify uop)
>   where OpPrec _ pr = opPrec op pEnv
> fixRPrec p pEnv e1 op1 (InfixApply e2 op2 e3)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
>       InfixApply e1 op1 (InfixApply e2 op2 e3)
>   | pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
>       InfixApply (fixPrec p pEnv e1 op1 e2) op2 e3
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op1) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> fixRPrec _ _ e1 op e2 = InfixApply e1 op e2

\end{verbatim}
The functions \texttt{checkLSection} and \texttt{checkRSection} are
used for handling the precedences inside left and right sections.
These functions only need to check that an infix operator occurring in
the section has either a higher precedence than the section operator
or both operators have the same precedence and are both left
associative for a left section and right associative for a right
section, respectively.
\begin{verbatim}

> checkLSection :: Position -> PEnv -> InfixOp -> Expression -> Expression
> checkLSection p pEnv op e@(UnaryMinus uop _)
>   | pr < 6 || pr == 6 && fix == InfixL = LeftSection e op
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op)
>   where OpPrec fix pr = opPrec op pEnv
> checkLSection p pEnv op1 e@(InfixApply _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
>       LeftSection e op1
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op1) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> checkLSection _ _ op e = LeftSection e op

> checkRSection :: Position -> PEnv -> InfixOp -> Expression -> Expression
> checkRSection p pEnv op e@(UnaryMinus uop _)
>   | pr < 6 = RightSection op e
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op)
>   where OpPrec _ pr = opPrec op pEnv
> checkRSection p pEnv op1 e@(InfixApply _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
>       RightSection op1 e
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op1) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> checkRSection _ _ op e = RightSection op e

\end{verbatim}
The functions \texttt{fixPrecT} and \texttt{fixRPrecT} check the
relative precedences of adjacent infix operators in patterns. The
patterns will be reordered such that the infix operator with the
lowest precedence becomes the root of the term. \emph{The functions
rely on the fact that the parser constructs infix patterns in a
right-associative fashion}, i.e., the left argument of an infix
pattern is never an infix pattern. The functions also check whether
the left and right arguments of an infix pattern are negative
literals. In that case, the operator's precedence must be lower than
that of unary negation.
\begin{verbatim}

> fixPrecT :: Position -> PEnv -> ConstrTerm -> QualIdent -> ConstrTerm
>          -> ConstrTerm
> fixPrecT p pEnv t1@(NegativePattern uop l) op t2
>   | pr < 6 || pr == 6 && fix == InfixL = fixRPrecT p pEnv t1 op t2
>   | otherwise = errorAt p $ invalidParse "unary" uop op
>   where OpPrec fix pr = prec op pEnv
> fixPrecT p pEnv t1 op t2 = fixRPrecT p pEnv t1 op t2

> fixRPrecT :: Position -> PEnv -> ConstrTerm -> QualIdent -> ConstrTerm
>           -> ConstrTerm
> fixRPrecT p pEnv t1 op t2@(NegativePattern uop l)
>   | pr < 6 = InfixPattern t1 op t2
>   | otherwise = errorAt p $ invalidParse "unary" uop op
>   where OpPrec _ pr = prec op pEnv
> fixRPrecT p pEnv t1 op1 (InfixPattern t2 op2 t3)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
>       InfixPattern t1 op1 (InfixPattern t2 op2 t3)
>   | pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
>       InfixPattern (fixPrecT p pEnv t1 op1 t2) op2 t3
>   | otherwise = errorAt p $ ambiguousParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec op1 pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> fixRPrecT _ _ t1 op t2 = InfixPattern t1 op t2

\end{verbatim}
The functions \texttt{checkOpL} and \texttt{checkOpR} check the left
and right arguments of an operator declaration. If they are infix
patterns they must bind more tightly than the operator, otherwise the
left-hand side of the declaration is invalid.
\begin{verbatim}

> checkOpL :: Position -> PEnv -> Ident -> ConstrTerm -> ConstrTerm
> checkOpL p pEnv op t@(NegativePattern uop l)
>   | pr < 6 || pr == 6 && fix == InfixL = t
>   | otherwise = errorAt p $ invalidParse "unary" uop (qualify op)
>   where OpPrec fix pr = prec (qualify op) pEnv
> checkOpL p pEnv op1 t@(InfixPattern _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL = t
>   | otherwise = errorAt p $ invalidParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec (qualify op1) pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> checkOpL _ _ _ t = t

> checkOpR :: Position -> PEnv -> Ident -> ConstrTerm -> ConstrTerm
> checkOpR p pEnv op t@(NegativePattern uop l)
>   | pr < 6 = t
>   | otherwise = errorAt p $ invalidParse "unary" uop (qualify op)
>   where OpPrec _ pr = prec (qualify op) pEnv
> checkOpR p pEnv op1 t@(InfixPattern _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR = t
>   | otherwise = errorAt p $ invalidParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec (qualify op1) pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> checkOpR _ _ _ t = t

\end{verbatim}
The functions \texttt{opPrec} and \texttt{prec} return the
associativity and operator precedence of an entity. Even though
precedence checking is performed after the renaming phase, we have to
be prepared for ambiguous identifiers here. This may happen while
checking the root of an operator definition that shadows an imported
definition.
\begin{verbatim}

> opPrec :: InfixOp -> PEnv -> OpPrec
> opPrec op = prec (opName op)

> prec :: QualIdent -> PEnv -> OpPrec
> prec op env =
>   case qualLookupP op env of
>     [] -> defaultP
>     PrecInfo _ p : _ -> p

\end{verbatim}
Error messages.
\begin{verbatim}

> invalidParse :: String -> Ident -> QualIdent -> String
> invalidParse what op1 op2 =
>   "Invalid use of " ++ what ++ " " ++ name op1 ++ " with " ++ qualName op2

> ambiguousParse :: String -> QualIdent -> QualIdent -> String
> ambiguousParse what op1 op2 =
>   "Ambiguous use of " ++ what ++ " " ++ qualName op1 ++
>   " with " ++ qualName op2

\end{verbatim}
