% -*- LaTeX -*-
% $Id: Desugar.lhs 1759 2005-09-03 10:41:38Z wlux $
%
% Copyright (c) 2001-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}
The desugaring pass removes all syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item All function definitions are $\eta$-expanded.
\item No guarded right hand sides occur in equations, pattern
  declarations, and case alternatives. In addition, the declaration
  lists of the right hand sides are empty; local declarations are
  transformed into let expressions.
\item Patterns in equations and case alternatives are composed only of
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructor applications, and
  \item as patterns.
  \end{itemize}
\item Expressions are composed only of
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructors,
  \item (binary) applications,
  \item let expressions, and
  \item case expressions.
  \end{itemize}
\item Applications $N\:x$ in patterns and expressions, where $N$ is a
  newtype constructor, are replaced by a $x$. Note that neither the
  newtype declaration itself nor partial applications of newtype
  constructors are changed.\footnote{It were possible to replace
  partial applications of newtype constructor by \texttt{prelude.id}.
  However, our solution yields a more accurate output when the result
  of a computation includes partial applications.}
\end{itemize}

\ToDo{Use a different representation for the restricted code instead
of using the syntax tree from \texttt{CurrySyntax}.}

\textbf{As we are going to insert references to real prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Desugar(desugar,desugarGoal) where
> import Base
> import Combined
> import List
> import Monad
> import Typing
> import Utils

\end{verbatim}
New identifiers may be introduced while desugaring pattern
declarations, case and $\lambda$-expressions, and list comprehensions.
As usual, we use a state monad transformer for generating unique
names. In addition, the state is also used for passing through the
type environment, which must be augmented with the types of these new
variables.
\begin{verbatim}

> type DesugarState a = StateT ValueEnv (StateT Int Id) a

> run :: DesugarState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. As type declarations are not desugared and
cannot occur in local declaration groups they are filtered out
separately.

Actually, the transformation is slightly more general than necessary,
as it allows pattern and free variable declarations at the top-level
of a module.
\begin{verbatim}

> desugar :: ValueEnv -> Module -> (Module,ValueEnv)
> desugar tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (desugarModule m ds) tyEnv

> desugarModule :: ModuleIdent -> [TopDecl] -> DesugarState ([TopDecl],ValueEnv)
> desugarModule m ds =
>   do
>     vds' <- desugarDeclGroup m [d | BlockDecl d <- vds]
>     tyEnv' <- fetchSt
>     return (tds ++ map BlockDecl vds',tyEnv')
>   where (tds,vds) = partition isTypeDecl ds

\end{verbatim}
While a goal of type \texttt{IO \_} is executed directly by the
runtime system, all other goals are evaluated under an interactive
top-level which displays the solutions of the goal and in particular
the bindings of the free variables. For this reason, the free
variables declared in the \texttt{where} clause of a goal are
translated into free variables of the goal. In addition, the goal
is transformed into a first order expression by performing a
unification with another variable. Thus, a goal
\begin{quote}
 \emph{expr}
 \texttt{where} $v_1$,\dots,$v_n$ \texttt{free}; \emph{decls}
\end{quote}
where no free variable declarations occur in \emph{decls} is
translated into the function
\begin{quote}
  \emph{f} $v_0$ $v_1$ \dots{} $v_n$ \texttt{=}
    $v_0$ \texttt{=:=} \emph{expr}
    \texttt{where} \emph{decls}
\end{quote}
where $v_0$ is a fresh variable.

\textbf{Note:} The debugger assumes that the goal is always a nullary
function. This means that we must not $\eta$-expand functional goal
expressions. In order to avoid the $\eta$-expansion we cheat a little
bit here and change the type of the goal into $\forall\alpha.\alpha$
if it really has a functional type.

\ToDo{Fix the debugger to handle functional goals so that this
hack is no longer needed.}
\begin{verbatim}

> desugarGoal :: Bool -> ValueEnv -> ModuleIdent -> Ident -> Goal
>             -> (Maybe [Ident],Module,ValueEnv)
> desugarGoal debug tyEnv m g (Goal p e ds)
>   | debug || isIO ty =
>       desugarGoalIO tyEnv p m g (Let ds e)
>         (if debug && arrowArity ty > 0 then typeVar 0 else ty)
>   | otherwise = desugarGoal' tyEnv p m g vs e' ty
>   where ty = typeOf tyEnv e
>         (vs,e') = liftGoalVars (if null ds then e else Let ds e)
>         isIO (TypeConstructor tc [_]) = tc == qIOId
>         isIO _ = False

> desugarGoalIO :: ValueEnv -> Position -> ModuleIdent -> Ident
>               -> Expression -> Type -> (Maybe [Ident],Module,ValueEnv)
> desugarGoalIO tyEnv p m g e ty =
>   (Nothing,
>    Module m Nothing [] [goalDecl p g [] e'],
>    bindFun m g (polyType ty) tyEnv')
>   where (e',tyEnv') = run (desugarGoalExpr m e) tyEnv

> desugarGoal' :: ValueEnv -> Position -> ModuleIdent -> Ident -> [Ident]
>              -> Expression -> Type -> (Maybe [Ident],Module,ValueEnv)
> desugarGoal' tyEnv p m g vs e ty =
>   (Just vs',
>    Module m Nothing [] [goalDecl p g (v0:vs') (apply prelUnif [mkVar v0,e'])],
>    bindFun m v0 (monoType ty) (bindFun m g (polyType ty') tyEnv'))
>   where (e',tyEnv') = run (desugarGoalExpr m e) tyEnv
>         v0 = anonId
>         vs' = filter (`elem` qfv m e') vs
>         ty' = TypeArrow ty (foldr (TypeArrow . typeOf tyEnv) successType vs')

> goalDecl :: Position -> Ident -> [Ident] -> Expression -> TopDecl
> goalDecl p g vs e = BlockDecl (funDecl p g (map VariablePattern vs) e)

> desugarGoalExpr :: ModuleIdent -> Expression
>                 -> DesugarState (Expression,ValueEnv)
> desugarGoalExpr m e =
>   do
>     e' <- desugarExpr m (first "") e
>     tyEnv' <- fetchSt
>     return (e',tyEnv')

> liftGoalVars :: Expression -> ([Ident],Expression)
> liftGoalVars (Let ds e) = (concat [vs | FreeDecl _ vs <- vds],Let ds' e)
>   where (vds,ds') = partition isFreeDecl ds
> liftGoalVars e = ([],e)

\end{verbatim}
Within a declaration group, all fixity declarations, type signatures
and evaluation annotations are discarded. First, the patterns
occurring in the left hand sides are desugared. Due to lazy patterns
this may add further declarations to the group that must be desugared
as well.
\begin{verbatim}

> desugarDeclGroup :: ModuleIdent -> [Decl] -> DesugarState [Decl]
> desugarDeclGroup m ds =
>   do
>     dss' <- mapM (desugarDeclLhs m) (filter isValueDecl ds)
>     mapM (desugarDeclRhs m) (concat dss')

> desugarDeclLhs :: ModuleIdent -> Decl -> DesugarState [Decl]
> desugarDeclLhs m (PatternDecl p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     dss' <- mapM (desugarDeclLhs m) ds'
>     return (PatternDecl p t' rhs : concat dss')
> desugarDeclLhs _ d = return [d]

\end{verbatim}
After desugaring its right hand side, each equation is $\eta$-expanded
by adding as many variables as necessary to the argument list and
applying the right hand side to those variables. The import entity
specification of foreign functions using the \texttt{ccall} calling
convention is expanded to always include the kind of the declaration
(either \texttt{static} or \texttt{dynamic}) and the name of the
imported function.
\begin{verbatim}

> desugarDeclRhs :: ModuleIdent -> Decl -> DesugarState Decl
> desugarDeclRhs m (FunctionDecl p f eqs) =
>   do
>     ty <- liftM (flip typeOf (Variable (qual f))) fetchSt
>     liftM (FunctionDecl p f) (mapM (desugarEquation m (arrowArgs ty)) eqs)
>   where qual f
>           | unRenameIdent f == f = qualifyWith m f
>           | otherwise = qualify f
> desugarDeclRhs _ (ForeignDecl p cc ie f ty) =
>   return (ForeignDecl p cc (desugarImpEnt cc ie) f ty)
>   where desugarImpEnt CallConvPrimitive ie = ie `mplus` Just (name f)
>         desugarImpEnt CallConvCCall ie =
>           Just (unwords (kind (maybe [] words ie)))
>         kind [] = "static" : ident []
>         kind (x:xs)
>           | x == "static" = x : ident xs
>           | x == "dynamic" = [x]
>           | otherwise = "static" : ident (x:xs)
>         ident [] = [name f]
>         ident [x]
>           | x == "&" || ".h" `isSuffixOf` x = [x,name f]
>           | otherwise = [x]
>         ident [h,x]
>           | x == "&" = [h,x,name f]
>           | otherwise = [h,x]
>         ident [h,amp,f] = [h,amp,f]
>         ident _ = internalError "desugarImpEnt CallConvCCall"
> desugarDeclRhs m (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (desugarRhs m p rhs)
> desugarDeclRhs _ (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: ModuleIdent -> [Type] -> Equation -> DesugarState Equation
> desugarEquation m tys (Equation p lhs rhs) =
>   do
>     vs <- mapM (freshIdent m "_#eta" . monoType) (drop (length ts) tys)
>     (ds',ts') <- mapAccumM (desugarTerm m p) [] ts
>     rhs' <- desugarRhs m p (addDecls ds' rhs)
>     return (Equation p (FunLhs f (ts' ++ map VariablePattern vs))
>                      (applyRhs rhs' (map mkVar vs)))
>   where (f,ts) = flatLhs lhs
>         applyRhs (SimpleRhs p e _) vs = SimpleRhs p (apply e vs) []

\end{verbatim}
The transformation of patterns is straight forward except for lazy
patterns. A lazy pattern \texttt{\~}$t$ is replaced by a fresh
variable $v$ and a new local declaration $t$~\texttt{=}~$v$ in the
scope of the pattern. In addition, as-patterns $v$\texttt{@}$t$ where
$t$ is a variable or an as-pattern are replaced by $t$ in combination
with a local declaration for $v$.
\begin{verbatim}

> desugarLiteral :: Literal -> DesugarState (Either Literal [Literal])
> desugarLiteral (Char c) = return (Left (Char c))
> desugarLiteral (Int v i) = liftM (Left . fixType) fetchSt
>   where fixType tyEnv
>           | typeOf tyEnv v == floatType = Float (fromIntegral i) 
>           | otherwise = Int v i
> desugarLiteral (Float f) = return (Left (Float f))
> desugarLiteral (String cs) = return (Right (map Char cs))

> desugarTerm :: ModuleIdent -> Position -> [Decl] -> ConstrTerm
>             -> DesugarState ([Decl],ConstrTerm)
> desugarTerm m p ds (LiteralPattern l) =
>   desugarLiteral l >>=
>   either (return . (,) ds . LiteralPattern)
>          (desugarTerm m p ds . ListPattern . map LiteralPattern)
> desugarTerm m p ds (NegativePattern _ l) =
>   desugarTerm m p ds (LiteralPattern (negateLiteral l))
>   where negateLiteral (Int v i) = Int v (-i)
>         negateLiteral (Float f) = Float (-f)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm _ _ ds (VariablePattern v) = return (ds,VariablePattern v)
> desugarTerm m p ds (ConstructorPattern c [t]) =
>   do
>     tyEnv <- fetchSt
>     liftM (if isNewtypeConstr tyEnv c then id else apSnd (constrPat c))
>           (desugarTerm m p ds t)
>   where constrPat c t = ConstructorPattern c [t]
> desugarTerm m p ds (ConstructorPattern c ts) =
>   liftM (apSnd (ConstructorPattern c)) (mapAccumM (desugarTerm m p) ds ts)
> desugarTerm m p ds (InfixPattern t1 op t2) =
>   desugarTerm m p ds (ConstructorPattern op [t1,t2])
> desugarTerm m p ds (ParenPattern t) = desugarTerm m p ds t
> desugarTerm m p ds (TuplePattern ts) =
>   desugarTerm m p ds (ConstructorPattern (tupleConstr ts) ts)
>   where tupleConstr ts = if null ts then qUnitId else qTupleId (length ts)
> desugarTerm m p ds (ListPattern ts) =
>   liftM (apSnd (foldr cons nil)) (mapAccumM (desugarTerm m p) ds ts)
>   where nil = ConstructorPattern qNilId []
>         cons t ts = ConstructorPattern qConsId [t,ts]
> desugarTerm m p ds (AsPattern v t) =
>   liftM (desugarAs p v) (desugarTerm m p ds t)
> desugarTerm m p ds (LazyPattern t) = desugarLazy m p ds t

> desugarAs :: Position -> Ident -> ([Decl],ConstrTerm) -> ([Decl],ConstrTerm)
> desugarAs p v (ds,t) =
>  case t of
>    VariablePattern v' -> (varDecl p v (mkVar v') : ds,t)
>    AsPattern v' _ -> (varDecl p v (mkVar v') : ds,t)
>    _ -> (ds,AsPattern v t)

> desugarLazy :: ModuleIdent -> Position -> [Decl] -> ConstrTerm
>             -> DesugarState ([Decl],ConstrTerm)
> desugarLazy m p ds t =
>   case t of
>     VariablePattern _ -> return (ds,t)
>     ParenPattern t' -> desugarLazy m p ds t'
>     AsPattern v t' -> liftM (desugarAs p v) (desugarLazy m p ds t')
>     LazyPattern t' -> desugarLazy m p ds t'
>     _ ->
>       do
>         v' <- fetchSt >>= freshIdent m "_#lazy" . monoType . flip typeOf t
>         return (patDecl p t (mkVar v') : ds,VariablePattern v')

\end{verbatim}
A list of boolean guards is expanded into a nested if-then-else
expression, whereas a constraint guard is replaced by a case
expression. Note that if the guard type is \texttt{Success} only a
single guard is allowed for each equation.\footnote{This change was
introduced in version 0.8 of the Curry report.} We check for the
type \texttt{Bool} of the guard because the guard's type defaults to
\texttt{Success} if it is not restricted by the guard expression.
\begin{verbatim}

> desugarRhs :: ModuleIdent -> Position -> Rhs -> DesugarState Rhs
> desugarRhs m p rhs =
>   do
>     tyEnv <- fetchSt
>     e' <- desugarExpr m p (expandRhs tyEnv prelFailed rhs)
>     return (SimpleRhs p e' [])

> expandRhs :: ValueEnv -> Expression -> Rhs -> Expression
> expandRhs tyEnv _ (SimpleRhs _ e ds) = Let ds e
> expandRhs tyEnv e0 (GuardedRhs es ds) = Let ds (expandGuards tyEnv e0 es)

> expandGuards :: ValueEnv -> Expression -> [CondExpr] -> Expression
> expandGuards tyEnv e0 es
>   | booleanGuards tyEnv es = foldr mkIfThenElse e0 es
>   | otherwise = mkCase es
>   where mkIfThenElse (CondExpr _ g e) = IfThenElse g e
>         mkCase [CondExpr p g e] = Case g [caseAlt p successPattern e]

> booleanGuards :: ValueEnv -> [CondExpr] -> Bool
> booleanGuards _ [] = False
> booleanGuards tyEnv (CondExpr _ g _ : es) =
>   not (null es) || typeOf tyEnv g == boolType

> desugarExpr :: ModuleIdent -> Position -> Expression
>             -> DesugarState Expression
> desugarExpr m p (Literal l) =
>   desugarLiteral l >>=
>   either (return . Literal) (desugarExpr m p . List . map Literal)
> desugarExpr _ _ (Variable v) = return (Variable v)
> desugarExpr _ _ (Constructor c) = return (Constructor c)
> desugarExpr m p (Paren e) = desugarExpr m p e
> desugarExpr m p (Typed e _) = desugarExpr m p e
> desugarExpr m p (Tuple es) =
>   liftM (apply (Constructor (tupleConstr es))) (mapM (desugarExpr m p) es)
>   where tupleConstr es = if null es then qUnitId else qTupleId (length es)
> desugarExpr m p (List es) =
>   liftM (foldr cons nil) (mapM (desugarExpr m p) es)
>   where nil = Constructor qNilId
>         cons = Apply . Apply (Constructor qConsId)
> desugarExpr m p (ListCompr e []) = desugarExpr m p (List [e])
> desugarExpr m p (ListCompr e (q:qs)) = desugarQual m p q (ListCompr e qs)
> desugarExpr m p (EnumFrom e) = liftM (Apply prelEnumFrom) (desugarExpr m p e)
> desugarExpr m p (EnumFromThen e1 e2) =
>   liftM (apply prelEnumFromThen) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromTo e1 e2) =
>   liftM (apply prelEnumFromTo) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply prelEnumFromThenTo) (mapM (desugarExpr m p) [e1,e2,e3])
> desugarExpr m p (UnaryMinus op e) =
>   do
>     tyEnv <- fetchSt
>     liftM (Apply (unaryMinus op (typeOf tyEnv e))) (desugarExpr m p e)
>   where unaryMinus op ty
>           | op == minusId =
>               if ty == floatType then prelNegateFloat else prelNegate
>           | op == fminusId = prelNegateFloat
>           | otherwise = internalError "unaryMinus"
> desugarExpr m p (Apply (Constructor c) e) =
>   do
>     tyEnv <- fetchSt
>     liftM (if isNewtypeConstr tyEnv c then id else (Apply (Constructor c)))
>           (desugarExpr m p e)
> desugarExpr m p (Apply e1 e2) =
>   do
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     return (Apply e1' e2')
> desugarExpr m p (InfixApply e1 op e2) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     return (Apply (Apply op' e1') e2')
> desugarExpr m p (LeftSection e op) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e' <- desugarExpr m p e
>     return (Apply op' e')
> desugarExpr m p (RightSection op e) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e' <- desugarExpr m p e
>     return (Apply (Apply prelFlip op') e')
> desugarExpr m p (Lambda ts e) =
>   do
>     f <- fetchSt >>=
>          freshIdent m "_#lambda" . polyType . flip typeOf (Lambda ts e)
>     desugarExpr m p (Let [funDecl p f ts e] (mkVar f))
> desugarExpr m p (Let ds e) =
>   do
>     ds' <- desugarDeclGroup m ds
>     e' <- desugarExpr m p e
>     return (if null ds' then e' else Let ds' e')
> desugarExpr m p (Do sts e) = desugarExpr m p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' = apply prelBind_ [e,e']
>         desugarStmt (StmtBind t e) e' = apply prelBind [e,Lambda [t] e']
>         desugarStmt (StmtDecl ds) e' = Let ds e'
> desugarExpr m p (IfThenElse e1 e2 e3) =
>   do
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     e3' <- desugarExpr m p e3
>     return (Case e1' [caseAlt p truePattern e2',caseAlt p falsePattern e3'])
> desugarExpr m p (Case e alts)
>   | null alts = return prelFailed
>   | otherwise =
>       do
>         e' <- desugarExpr m p e
>         v <- fetchSt >>= freshIdent m "_#case" . monoType . flip typeOf e
>         alts' <- mapM (desugarAltLhs m) alts
>         tyEnv <- fetchSt
>         alts'' <- mapM (desugarAltRhs m)
>                        (map (expandAlt tyEnv v) (init (tails alts')))
>         return (mkCase m v e' alts'')
>   where mkCase m v e alts
>           | v `elem` qfv m alts = Let [varDecl p v e] (Case (mkVar v) alts)
>           | otherwise = Case e alts

\end{verbatim}
If an alternative in a case expression has boolean guards and all of
these guards return \texttt{False}, the enclosing case expression does
not fail but continues to match the remaining alternatives against the
selector expression. In order to implement this semantics, which is
compatible with Haskell, we expand an alternative with boolean guards
such that it evaluates a case expression with the remaining cases that
are compatible with the matched pattern when the guards fail.
\begin{verbatim}

> desugarAltLhs :: ModuleIdent -> Alt -> DesugarState Alt
> desugarAltLhs m (Alt p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     return (Alt p t' (addDecls ds' rhs))

> desugarAltRhs :: ModuleIdent -> Alt -> DesugarState Alt
> desugarAltRhs m (Alt p t rhs) = liftM (Alt p t) (desugarRhs m p rhs)

> expandAlt :: ValueEnv -> Ident -> [Alt] -> Alt
> expandAlt tyEnv v (Alt p t rhs : alts) = caseAlt p t (expandRhs tyEnv e0 rhs)
>   where e0 = Case (mkVar v) (filter (isCompatible t . altPattern) alts)
>         altPattern (Alt _ t _) = t

> isCompatible :: ConstrTerm -> ConstrTerm -> Bool
> isCompatible (VariablePattern _) _ = True
> isCompatible _ (VariablePattern _) = True
> isCompatible (AsPattern _ t1) t2 = isCompatible t1 t2
> isCompatible t1 (AsPattern _ t2) = isCompatible t1 t2
> isCompatible (ConstructorPattern c1 ts1) (ConstructorPattern c2 ts2) =
>   and ((c1 == c2) : zipWith isCompatible ts1 ts2)
> isCompatible (LiteralPattern l1) (LiteralPattern l2) = canon l1 == canon l2
>   where canon (Int _ i) = Int anonId i
>         canon l = l

\end{verbatim}
In general, a list comprehension of the form
\texttt{[}$e$~\texttt{|}~$t$~\texttt{<-}~$l$\texttt{,}~\emph{qs}\texttt{]}
is transformed into an expression \texttt{foldr}~$f$~\texttt{[]}~$l$ where $f$
is a new function defined as
\begin{quote}
  \begin{tabbing}
    $f$ $x$ \emph{xs} \texttt{=} \\
    \quad \= \texttt{case} $x$ \texttt{of} \\
          \> \quad \= $t$ \texttt{->} \texttt{[}$e$ \texttt{|} \emph{qs}\texttt{]} \texttt{++} \emph{xs} \\
          \>       \> \texttt{\_} \texttt{->} \emph{xs}
  \end{tabbing}
\end{quote}
Note that this translation evaluates the elements of $l$ rigidly,
whereas the translation given in the Curry report is flexible.
However, it does not seem very useful to have the comprehension
generate instances of $t$ which do not contribute to the list.

Actually, we generate slightly better code in a few special cases.
When $t$ is a plain variable, the \texttt{case} expression degenerates
into a let-binding and the auxiliary function thus becomes an alias
for \texttt{(++)}. Instead of \texttt{foldr~(++)} we use the
equivalent prelude function \texttt{concatMap}. In addition, if the
remaining list comprehension in the body of the auxiliary function has
no qualifiers -- i.e., if it is equivalent to \texttt{[$e$]} -- we
avoid the construction of the singleton list by calling \texttt{(:)}
instead of \texttt{(++)} and \texttt{map} in place of
\texttt{concatMap}, respectively.
\begin{verbatim}

> desugarQual :: ModuleIdent -> Position -> Statement -> Expression
>             -> DesugarState Expression
> desugarQual m p (StmtExpr b) e = desugarExpr m p (IfThenElse b e (List []))
> desugarQual m p (StmtBind t l) e
>   | isVarPattern t = desugarExpr m p (qualExpr t e l)
>   | otherwise =
>       do
>         tyEnv <- fetchSt
>         v <- freshIdent m "_#var" (monoType (typeOf tyEnv t))
>         l' <- freshIdent m "_#var" (monoType (typeOf tyEnv e))
>         desugarExpr m p (apply prelFoldr [foldFunct v l' e,List [],l])
>   where qualExpr v (ListCompr e []) l = apply prelMap [Lambda [v] e,l]
>         qualExpr v e l = apply prelConcatMap [Lambda [v] e,l]
>         foldFunct v l e =
>           Lambda (map VariablePattern [v,l])
>             (Case (mkVar v)
>                   [caseAlt p t (append e (mkVar l)),
>                    caseAlt p (VariablePattern v) (mkVar l)])
>         append (ListCompr e []) l = apply (Constructor qConsId) [e,l]
>         append e l = apply prelAppend [e,l]
> desugarQual m p (StmtDecl ds) e = desugarExpr m p (Let ds e)

\end{verbatim}
Generation of fresh names
\begin{verbatim}

> freshIdent :: ModuleIdent -> String -> TypeScheme -> DesugarState Ident
> freshIdent m prefix ty =
>   do
>     x <- liftM (mkName prefix) (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m x ty)
>     return x
>   where mkName pre n = mkIdent (pre ++ show n)

\end{verbatim}
Prelude entities
\begin{verbatim}

> prelUnif = Variable $ preludeIdent "=:="
> prelBind = Variable $ preludeIdent ">>="
> prelBind_ = Variable $ preludeIdent ">>"
> prelFlip = Variable $ preludeIdent "flip"
> prelEnumFrom = Variable $ preludeIdent "enumFrom"
> prelEnumFromTo = Variable $ preludeIdent "enumFromTo"
> prelEnumFromThen = Variable $ preludeIdent "enumFromThen"
> prelEnumFromThenTo = Variable $ preludeIdent "enumFromThenTo"
> prelFailed = Variable $ preludeIdent "failed"
> prelMap = Variable $ preludeIdent "map"
> prelFoldr = Variable $ preludeIdent "foldr"
> prelAppend = Variable $ preludeIdent "++"
> prelConcatMap = Variable $ preludeIdent "concatMap"
> prelNegate = Variable $ preludeIdent "negate"
> prelNegateFloat = Variable $ preludeIdent "negateFloat"

> truePattern = ConstructorPattern qTrueId []
> falsePattern = ConstructorPattern qFalseId []
> successPattern = ConstructorPattern (qualify successId) []

> preludeIdent :: String -> QualIdent
> preludeIdent = qualifyWith preludeMIdent . mkIdent

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
> isNewtypeConstr tyEnv c =
>   case qualLookupValue c tyEnv of
>     [DataConstructor _ _] -> False
>     [NewtypeConstructor _ _] -> True
>     _ -> internalError "isNewtypeConstr"

> isVarPattern :: ConstrTerm -> Bool
> isVarPattern (VariablePattern _) = True
> isVarPattern (ParenPattern t) = isVarPattern t
> isVarPattern (AsPattern _ t) = isVarPattern t
> isVarPattern (LazyPattern _) = True
> isVarPattern _ = False

> funDecl :: Position -> Ident -> [ConstrTerm] -> Expression -> Decl
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> patDecl :: Position -> ConstrTerm -> Expression -> Decl
> patDecl p t e = PatternDecl p t (SimpleRhs p e [])

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p = patDecl p . VariablePattern

> addDecls :: [Decl] -> Rhs -> Rhs
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

> caseAlt :: Position -> ConstrTerm -> Expression -> Alt
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> apply :: Expression -> [Expression] -> Expression
> apply = foldl Apply

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

\end{verbatim}
