% -*- LaTeX -*-
% $Id: Desugar.lhs 2961 2010-06-15 15:37:14Z wlux $
%
% Copyright (c) 2001-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}\label{sec:desugar}
The desugaring pass removes most syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item Patterns in equations and (f)case alternatives are composed of only
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructor applications,
  \item function applications (function patterns),
  \item record patterns,
  \item as-patterns, and
  \item lazy patterns.
  \end{itemize}
\item Expressions are composed of only
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructors,
  \item record constructions and updates,
  \item (binary) applications,
  \item lambda abstractions,
  \item let expressions, and
  \item (f)case expressions.
  \end{itemize}
\end{itemize}
Note that some syntactic sugar remains. In particular, we do not
replace boolean guards by if-then-else cascades and we do not
transform where clauses into let expressions. Both will happen only
after flattening patterns in case expressions, as this allows us to
handle the fall through behavior of boolean guards in case expressions
without introducing a special pattern match failure primitive (see
Sect.~\ref{sec:flatcase}). We also do not desugar lazy patterns and
the record syntax here. These are taken care of by ensuing compiler
phases.

\textbf{As we are going to insert references to real Prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Desugar(desugar) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import Types
> import Typing
> import ValueInfo

\end{verbatim}
New identifiers may be introduced while desugaring list
comprehensions. As usual, we use a state monad transformer for
generating unique names. In addition, the state is also used for
passing through the type environment, which is augmented with the
types of the new variables.
\begin{verbatim}

> type DesugarState a = StateT ValueEnv (StateT Int Id) a

> run :: DesugarState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. At the top-level of a module, we just
desugar data constructor declarations. The top-level function
declarations are treated like a global declaration group.
\begin{verbatim}

> desugar :: ValueEnv -> Module Type -> (Module Type,ValueEnv)
> desugar tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (desugarModule m ds) tyEnv

> desugarModule :: ModuleIdent -> [TopDecl Type]
>               -> DesugarState ([TopDecl Type],ValueEnv)
> desugarModule m ds =
>   do
>     vds' <- desugarDeclGroup m [d | BlockDecl d <- vds]
>     tyEnv' <- fetchSt
>     return (map desugarTopDecl tds ++ map BlockDecl vds',tyEnv')
>   where (vds,tds) = partition isBlockDecl ds

> desugarTopDecl :: TopDecl a -> TopDecl a
> desugarTopDecl (DataDecl p tc tvs cs) =
>   DataDecl p tc tvs (map desugarConstrDecl cs)
>   where desugarConstrDecl (ConstrDecl p evs c tys) = ConstrDecl p evs c tys
>         desugarConstrDecl (ConOpDecl p evs ty1 op ty2) =
>           ConstrDecl p evs op [ty1,ty2]
>         desugarConstrDecl (RecordDecl p evs c fs) = RecordDecl p evs c fs
> desugarTopDecl (NewtypeDecl p tc tvs nc) = NewtypeDecl p tc tvs nc
> desugarTopDecl (TypeDecl p tc tvs ty) = TypeDecl p tc tvs ty
> --desugarTopDecl (BlockDecl d) = BlockDecl d
> desugarTopDecl (SplitAnnot p) = SplitAnnot p

\end{verbatim}
Within a declaration group, all fixity declarations, type signatures,
and trust annotations are discarded. The import entity specification
of foreign function declarations using the \texttt{ccall} and
\texttt{rawcall} calling conventions is expanded to always include the
kind of the declaration (either \texttt{static} or \texttt{dynamic})
and the name of the imported function.
\begin{verbatim}

> desugarDeclGroup :: ModuleIdent -> [Decl Type] -> DesugarState [Decl Type]
> desugarDeclGroup m ds = mapM (desugarDecl m) (filter isValueDecl ds)

> desugarDecl :: ModuleIdent -> Decl Type -> DesugarState (Decl Type)
> desugarDecl m (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (desugarEquation m) eqs)
> desugarDecl _ (ForeignDecl p (cc,s,ie) f ty) =
>   return (ForeignDecl p (cc,s `mplus` Just Safe,desugarImpEnt cc ie) f ty)
>   where desugarImpEnt cc ie
>           | cc == CallConvPrimitive = ie `mplus` Just (name f)
>           | otherwise = Just (unwords (kind (maybe [] words ie)))
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
>         ident _ = internalError "desugarImpEnt"
> desugarDecl m (PatternDecl p t rhs) =
>   liftM2 (PatternDecl p) (desugarTerm m t) (desugarRhs m rhs)
> desugarDecl _ (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: ModuleIdent -> Equation Type
>                 -> DesugarState (Equation Type)
> desugarEquation m (Equation p lhs rhs) =
>   liftM2 (Equation p . FunLhs f) (mapM (desugarTerm m) ts) (desugarRhs m rhs)
>   where (f,ts) = flatLhs lhs

\end{verbatim}
We expand each string literal in a pattern or expression into a list
of characters.
\begin{verbatim}

> desugarLiteral :: Type -> Literal -> Either Literal [Literal]
> desugarLiteral _ (Char c) = Left (Char c)
> desugarLiteral ty (Int i) = Left (fixType ty i)
>   where fixType ty i
>           | ty == floatType = Float (fromIntegral i)
>           | otherwise = Int i
> desugarLiteral _ (Float f) = Left (Float f)
> desugarLiteral _ (String cs) = Right (map Char cs)

> desugarTerm :: ModuleIdent -> ConstrTerm Type
>             -> DesugarState (ConstrTerm Type)
> desugarTerm m (LiteralPattern ty l) =
>   either (return . LiteralPattern ty)
>          (desugarTerm m . ListPattern ty . map (LiteralPattern ty'))
>          (desugarLiteral ty l)
>   where ty' = elemType ty
> desugarTerm m (NegativePattern ty _ l) =
>   desugarTerm m (LiteralPattern ty (negateLiteral l))
>   where negateLiteral (Int i) = Int (-i)
>         negateLiteral (Float f) = Float (-f)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm _ (VariablePattern ty v) = return (VariablePattern ty v)
> desugarTerm m (ConstructorPattern ty c ts) =
>   liftM (ConstructorPattern ty c) (mapM (desugarTerm m) ts)
> desugarTerm m (FunctionPattern ty f ts) =
>   liftM (FunctionPattern ty f) (mapM (desugarTerm m) ts)
> desugarTerm m (InfixPattern ty t1 op t2) =
>   desugarTerm m (desugarOp ty op [t1,t2])
>   where desugarOp ty (InfixConstr _ op) = ConstructorPattern ty op
>         desugarOp ty (InfixOp _ op) = FunctionPattern ty op
> desugarTerm m (ParenPattern t) = desugarTerm m t
> desugarTerm m (RecordPattern ty c fs) =
>   liftM (RecordPattern ty c) (mapM (desugarField (desugarTerm m)) fs)
> desugarTerm m (TuplePattern ts) =
>   desugarTerm m (ConstructorPattern ty (qTupleId (length ts)) ts)
>   where ty = tupleType (map typeOf ts)
> desugarTerm m (ListPattern ty ts) =
>   liftM (foldr cons nil) (mapM (desugarTerm m) ts)
>   where nil = ConstructorPattern ty qNilId []
>         cons t ts = ConstructorPattern ty qConsId [t,ts]
> desugarTerm m (AsPattern v t) = liftM (AsPattern v) (desugarTerm m t)
> desugarTerm m (LazyPattern t) = liftM LazyPattern (desugarTerm m t)

\end{verbatim}
Anonymous identifiers in expressions are replaced by an expression
\texttt{let x free in x} where \texttt{x} is a fresh variable.
However, we must be careful with this transformation because the
compiler uses an anonymous identifier also for the name of the
program's initial goal (cf.\ Sect.~\ref{sec:goals}). This variable
must remain a free variable of the goal expression and therefore must
not be replaced.
\begin{verbatim}

> desugarRhs :: ModuleIdent -> Rhs Type -> DesugarState (Rhs Type)
> desugarRhs m (SimpleRhs p e ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     e' <- desugarExpr m p e
>     return (SimpleRhs p e' ds')
> desugarRhs m (GuardedRhs es ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     es' <- mapM (desugarCondExpr m) es
>     return (GuardedRhs es' ds')

> desugarCondExpr :: ModuleIdent -> CondExpr Type
>                 -> DesugarState (CondExpr Type)
> desugarCondExpr m (CondExpr p g e) =
>   liftM2 (CondExpr p) (desugarExpr m p g) (desugarExpr m p e)

> desugarExpr :: ModuleIdent -> Position -> Expression Type
>             -> DesugarState (Expression Type)
> desugarExpr m p (Literal ty l) =
>   either (return . Literal ty)
>          (desugarExpr m p . List ty . map (Literal (elemType ty)))
>          (desugarLiteral ty l)
> desugarExpr m p (Variable ty v)
>   -- NB The name of the initial goal is anonId (not renamed, cf. goalModule
>   --    in module Goals) and must not be changed
>   | isRenamed v' && unRenameIdent v' == anonId =
>       do
>         v'' <- freshVar m "_#var" ty
>         return (Let [FreeDecl p [snd v'']] (uncurry mkVar v''))
>   | otherwise = return (Variable ty v)
>   where v' = unqualify v
> desugarExpr _ _ (Constructor ty c) = return (Constructor ty c)
> desugarExpr m p (Paren e) = desugarExpr m p e
> desugarExpr m p (Typed e _) = desugarExpr m p e
> desugarExpr m p (Record ty c fs) =
>   liftM (Record ty c) (mapM (desugarField (desugarExpr m p)) fs)
> desugarExpr m p (RecordUpdate e fs) =
>   liftM2 RecordUpdate
>          (desugarExpr m p e)
>          (mapM (desugarField (desugarExpr m p)) fs)
> desugarExpr m p (Tuple es) =
>   liftM (apply (Constructor ty (qTupleId (length es))))
>         (mapM (desugarExpr m p) es)
>   where ty = foldr TypeArrow (tupleType tys) tys
>         tys = map typeOf es
> desugarExpr m p (List ty es) =
>   liftM (foldr cons nil) (mapM (desugarExpr m p) es)
>   where nil = Constructor ty qNilId
>         cons = Apply . Apply (Constructor (consType (elemType ty)) qConsId)
> desugarExpr m p (ListCompr e qs) =
>   desugarListCompr m e qs z >>= desugarExpr m p
>   where z = List (typeOf (ListCompr e qs)) []
> desugarExpr m p (EnumFrom e) = liftM (Apply prelEnumFrom) (desugarExpr m p e)
> desugarExpr m p (EnumFromThen e1 e2) =
>   liftM (apply prelEnumFromThen) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromTo e1 e2) =
>   liftM (apply prelEnumFromTo) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply prelEnumFromThenTo) (mapM (desugarExpr m p) [e1,e2,e3])
> desugarExpr m p (UnaryMinus op e) =
>   liftM (Apply (unaryMinus op (typeOf e))) (desugarExpr m p e)
>   where unaryMinus op ty
>           | op == minusId =
>               if ty == floatType then prelNegateFloat else prelNegate
>           | op == fminusId = prelNegateFloat
>           | otherwise = internalError "unaryMinus"
> desugarExpr m p (Apply e1 e2) =
>   liftM2 Apply (desugarExpr m p e1) (desugarExpr m p e2)
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
>     return (Apply (Apply (prelFlip ty1 ty2 ty3) op') e')
>   where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
> desugarExpr m _ (Lambda p ts e) =
>   liftM2 (Lambda p) (mapM (desugarTerm m) ts) (desugarExpr m p e)
> desugarExpr m p (Let ds e) =
>   liftM2 Let (desugarDeclGroup m ds) (desugarExpr m p e)
> desugarExpr m p (Do sts e) = desugarExpr m p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' =
>           apply (prelBind_ (ioResType (typeOf e)) (ioResType (typeOf e')))
>                 [e,e']
>         desugarStmt (StmtBind p t e) e' =
>           apply (prelBind (typeOf t) (ioResType (typeOf e')))
>                 [e,Lambda p [t] e']
>         desugarStmt (StmtDecl ds) e' = mkLet ds e'
> desugarExpr m p (IfThenElse e1 e2 e3) =
>   liftM3 mkCase (desugarExpr m p e1) (desugarExpr m p e2) (desugarExpr m p e3)
>   where mkCase e1 e2 e3 =
>           Case e1 [caseAlt p truePattern e2,caseAlt p falsePattern e3]
> desugarExpr m p (Case e as) =
>   liftM2 Case (desugarExpr m p e) (mapM (desugarAlt m) as)
> desugarExpr m p (Fcase e as) =
>   liftM2 Fcase (desugarExpr m p e) (mapM (desugarAlt m) as)

> desugarAlt :: ModuleIdent -> Alt Type -> DesugarState (Alt Type)
> desugarAlt m (Alt p t rhs) =
>   liftM2 (Alt p) (desugarTerm m t) (desugarRhs m rhs)

> desugarField :: (a -> DesugarState a) -> Field a -> DesugarState (Field a)
> desugarField desugar (Field l e) = liftM (Field l) (desugar e)

\end{verbatim}
List comprehensions are desugared with the following optimized
translation scheme, which constructs the denoted list with (nested)
foldr applications.
\begin{displaymath}
  \newcommand{\semant}[2]{\mathcal{#1}[\![#2]\!]}
  \renewcommand{\arraystretch}{1.2}
  \begin{array}{r@{\;}c@{\;}l}
    \semant{D}{\texttt{[$e$|$qs$]}} &=&
      \semant{L}{\texttt{[$e$|$qs$]}}(\texttt{[]}) \\
    \semant{L}{\texttt{[$e$|]}}(z) &=& \texttt{$e$:$z$} \\
    \semant{L}{\texttt{[$e$|$b$,$qs$]}}(z) &=&
      \texttt{if $b$ then $\semant{L}{\texttt{[$e$|$qs$]}}(z)$ else $z$} \\
    \semant{L}{\texttt{[$e$|$t$<-$l$,$qs$]}}(z) &=& \\
    \texttt{foldr} & \multicolumn{2}{l}{\texttt{(\char`\\$x$ $y$ -> case $x$ of \char`\{\
          $t$ -> $\semant{L}{\texttt{[$e$|$qs$]}}(y)$; \_ -> $y$ \char`\}) $z$ $l$}}\\
     \textrm{where} & \multicolumn{2}{@{}l}{\textrm{$x$, $y$ are fresh identifiers}} \\
    \semant{L}{\texttt{[$e$|let $ds$,$qs$]}}(z) &=&
      \texttt{let $ds$ in $\semant{L}{\texttt{[$e$|$qs$]}}(z)$} \\
  \end{array}
\end{displaymath}
Note that the transformation scheme uses a rigid case expression to
match the pattern of a \texttt{$t$<-$l$} qualifier, which differs from
the Curry report (cf.\ Sect.~5.2 in~\cite{Hanus:Report}). We use a
rigid match here because it makes the translation scheme simpler,
since we do not need to compute the set of patterns that are
incompatible with $t$ and we do not need a special case for literal
patterns. In addition, it looks dubious to have list comprehension
qualifiers generate fresh instances of $t$ that do not contribute to
the list at all.
\begin{verbatim}

> desugarListCompr :: ModuleIdent -> Expression Type -> [Statement Type]
>                  -> Expression Type -> DesugarState (Expression Type)
> desugarListCompr _ e [] z =
>   return (apply (Constructor (consType (typeOf e)) qConsId) [e,z])
> desugarListCompr m e (q:qs) z =
>   desugarQual m q z >>= \(y,f) -> desugarListCompr m e qs y >>= return . f

> desugarQual :: ModuleIdent -> Statement Type -> Expression Type
>             -> DesugarState (Expression Type,
>                              Expression Type -> Expression Type)
> desugarQual _ (StmtExpr b) z = return (z,\e -> IfThenElse b e z)
> desugarQual m (StmtBind p t l) z =
>   do
>     v <- freshVar m "_#var" (typeOf t)
>     y <- freshVar m "_#var" (typeOf z)
>     return (uncurry mkVar y,
>             \e -> apply (prelFoldr (fst v) (fst y)) [foldFunct v y e,z,l])
>   where foldFunct v l e =
>           Lambda p [uncurry VariablePattern v,uncurry VariablePattern l]
>             (Case (uncurry mkVar v)
>                   [caseAlt p t e,
>                    caseAlt p (uncurry VariablePattern v) (uncurry mkVar l)])
> desugarQual _ (StmtDecl ds) z = return (z,Let ds)

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: ModuleIdent -> String -> Type -> DesugarState (Type,Ident)
> freshVar m prefix ty =
>   do
>     v <- liftM (mkName prefix) (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m v 0 (monoType ty))
>     return (ty,v)
>   where mkName pre n = mkIdent (pre ++ show n)

\end{verbatim}
Prelude entities.
\begin{verbatim}

> prelBind a b = preludeFun [ioType a,a `TypeArrow` ioType b] (ioType b) ">>="
> prelBind_ a b = preludeFun [ioType a,ioType b] (ioType b) ">>"
> prelFlip a b c = preludeFun [a `TypeArrow` (b `TypeArrow` c),b,a] c "flip"
> prelEnumFrom = preludeFun [intType] (listType intType) "enumFrom"
> prelEnumFromTo = preludeFun [intType,intType] (listType intType) "enumFromTo"
> prelEnumFromThen =
>   preludeFun [intType,intType] (listType intType) "enumFromThen"
> prelEnumFromThenTo =
>   preludeFun [intType,intType,intType] (listType intType) "enumFromThenTo"
> prelFoldr a b =
>   preludeFun [a `TypeArrow` (b `TypeArrow` b),b,listType a] b "foldr"
> prelNegate = preludeFun [intType] intType "negate"
> prelNegateFloat = preludeFun [floatType] floatType "negateFloat"

> preludeFun :: [Type] -> Type -> String -> Expression Type
> preludeFun tys ty f =
>   Variable (foldr TypeArrow ty tys) (qualifyWith preludeMIdent (mkIdent f))

> truePattern, falsePattern :: ConstrTerm Type
> truePattern = ConstructorPattern boolType qTrueId []
> falsePattern = ConstructorPattern boolType qFalseId []

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> consType :: Type -> Type
> consType a = TypeArrow a (TypeArrow (listType a) (listType a))

> elemType :: Type -> Type
> elemType (TypeConstructor tc [ty]) | tc == qListId = ty
> elemType ty = internalError ("elemType " ++ show ty)

> ioResType :: Type -> Type
> ioResType (TypeConstructor tc [ty]) | tc == qIOId = ty
> ioResType ty = internalError ("ioResType " ++ show ty)

\end{verbatim}
