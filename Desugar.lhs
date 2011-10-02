% -*- LaTeX -*-
% $Id: Desugar.lhs 3048 2011-10-02 14:14:03Z wlux $
%
% Copyright (c) 2001-2011, Wolfgang Lux
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

\end{verbatim}
New identifiers may be introduced while desugaring list
comprehensions. As usual, we use a state monad transformer for
generating unique names.
\begin{verbatim}

> type DesugarState a = StateT Int Id a

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. At the top-level of a module, we just
desugar data constructor declarations. The top-level function
declarations are treated like a global declaration group.
\begin{verbatim}

> desugar :: Module Type -> Module Type
> desugar (Module m es is ds) = Module m es is (runSt (desugarModule ds) 1)

> desugarModule :: [TopDecl Type] -> DesugarState [TopDecl Type]
> desugarModule ds =
>   do
>     vds' <- desugarDeclGroup [d | BlockDecl d <- vds]
>     return (map desugarTopDecl tds ++ map BlockDecl vds')
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

\end{verbatim}
Within a declaration group, all fixity declarations, type signatures,
and trust annotations are discarded. The import entity specification
of foreign function declarations using the \texttt{ccall} and
\texttt{rawcall} calling conventions is expanded to always include the
kind of the declaration (either \texttt{static} or \texttt{dynamic})
and the name of the imported function.
\begin{verbatim}

> desugarDeclGroup :: [Decl Type] -> DesugarState [Decl Type]
> desugarDeclGroup ds = mapM desugarDecl (filter isValueDecl ds)

> desugarDecl :: Decl Type -> DesugarState (Decl Type)
> desugarDecl (FunctionDecl p ty f eqs) =
>   liftM (FunctionDecl p ty f) (mapM desugarEquation eqs)
> desugarDecl (ForeignDecl p (cc,s,ie) ty f ty') =
>   return (ForeignDecl p (cc,s `mplus` Just Safe,desugarImpEnt cc ie) ty f ty')
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
> desugarDecl (PatternDecl p t rhs) =
>   liftM2 (PatternDecl p) (desugarTerm t) (desugarRhs rhs)
> desugarDecl (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: Equation Type -> DesugarState (Equation Type)
> desugarEquation (Equation p lhs rhs) =
>   liftM2 (Equation p . FunLhs f) (mapM desugarTerm ts) (desugarRhs rhs)
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

> desugarTerm :: ConstrTerm Type -> DesugarState (ConstrTerm Type)
> desugarTerm (LiteralPattern ty l) =
>   either (return . LiteralPattern ty)
>          (desugarTerm . ListPattern ty . map (LiteralPattern ty'))
>          (desugarLiteral ty l)
>   where ty' = elemType ty
> desugarTerm (NegativePattern ty _ l) =
>   desugarTerm (LiteralPattern ty (negateLiteral l))
>   where negateLiteral (Int i) = Int (-i)
>         negateLiteral (Float f) = Float (-f)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm (VariablePattern ty v) = return (VariablePattern ty v)
> desugarTerm (ConstructorPattern ty c ts) =
>   liftM (ConstructorPattern ty c) (mapM desugarTerm ts)
> desugarTerm (FunctionPattern ty f ts) =
>   liftM (FunctionPattern ty f) (mapM desugarTerm ts)
> desugarTerm (InfixPattern ty t1 op t2) = desugarTerm (desugarOp ty op [t1,t2])
>   where desugarOp ty (InfixConstr _ op) = ConstructorPattern ty op
>         desugarOp ty (InfixOp _ op) = FunctionPattern ty op
> desugarTerm (ParenPattern t) = desugarTerm t
> desugarTerm (RecordPattern ty c fs) =
>   liftM (RecordPattern ty c) (mapM (desugarField desugarTerm) fs)
> desugarTerm (TuplePattern ts) =
>   desugarTerm (ConstructorPattern ty (qTupleId (length ts)) ts)
>   where ty = tupleType (map typeOf ts)
> desugarTerm (ListPattern ty ts) = liftM (foldr cons nil) (mapM desugarTerm ts)
>   where nil = ConstructorPattern ty qNilId []
>         cons t ts = ConstructorPattern ty qConsId [t,ts]
> desugarTerm (AsPattern v t) = liftM (AsPattern v) (desugarTerm t)
> desugarTerm (LazyPattern t) = liftM LazyPattern (desugarTerm t)

\end{verbatim}
Anonymous identifiers in expressions are replaced by an expression
\texttt{let x free in x} where \texttt{x} is a fresh variable.
However, we must be careful with this transformation because the
compiler uses an anonymous identifier also for the name of the
program's initial goal (cf.\ Sect.~\ref{sec:goals}). This variable
must remain a free variable of the goal expression and therefore must
not be replaced.
\begin{verbatim}

> desugarRhs :: Rhs Type -> DesugarState (Rhs Type)
> desugarRhs (SimpleRhs p e ds) =
>   do
>     ds' <- desugarDeclGroup ds
>     e' <- desugarExpr p e
>     return (SimpleRhs p e' ds')
> desugarRhs (GuardedRhs es ds) =
>   do
>     ds' <- desugarDeclGroup ds
>     es' <- mapM desugarCondExpr es
>     return (GuardedRhs es' ds')

> desugarCondExpr :: CondExpr Type -> DesugarState (CondExpr Type)
> desugarCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (desugarExpr p g) (desugarExpr p e)

> desugarExpr :: Position -> Expression Type -> DesugarState (Expression Type)
> desugarExpr p (Literal ty l) =
>   either (return . Literal ty)
>          (desugarExpr p . List ty . map (Literal (elemType ty)))
>          (desugarLiteral ty l)
> desugarExpr p (Variable ty v)
>   -- NB The name of the initial goal is anonId (not renamed, cf. goalModule
>   --    in module Goals) and must not be changed
>   | isRenamed v' && unRenameIdent v' == anonId =
>       do
>         v'' <- freshVar "_#var" ty
>         return (Let [FreeDecl p [uncurry FreeVar v'']] (uncurry mkVar v''))
>   | otherwise = return (Variable ty v)
>   where v' = unqualify v
> desugarExpr _ (Constructor ty c) = return (Constructor ty c)
> desugarExpr p (Paren e) = desugarExpr p e
> desugarExpr p (Typed e _) = desugarExpr p e
> desugarExpr p (Record ty c fs) =
>   liftM (Record ty c) (mapM (desugarField (desugarExpr p)) fs)
> desugarExpr p (RecordUpdate e fs) =
>   liftM2 RecordUpdate
>          (desugarExpr p e)
>          (mapM (desugarField (desugarExpr p)) fs)
> desugarExpr p (Tuple es) =
>   liftM (apply (Constructor ty (qTupleId (length es))))
>         (mapM (desugarExpr p) es)
>   where ty = foldr TypeArrow (tupleType tys) tys
>         tys = map typeOf es
> desugarExpr p (List ty es) = liftM (foldr cons nil) (mapM (desugarExpr p) es)
>   where nil = Constructor ty qNilId
>         cons = Apply . Apply (Constructor (consType (elemType ty)) qConsId)
> desugarExpr p (ListCompr e qs) = desugarListCompr e qs z >>= desugarExpr p
>   where z = List (typeOf (ListCompr e qs)) []
> desugarExpr p (EnumFrom e) = liftM (Apply prelEnumFrom) (desugarExpr p e)
> desugarExpr p (EnumFromThen e1 e2) =
>   liftM (apply prelEnumFromThen) (mapM (desugarExpr p) [e1,e2])
> desugarExpr p (EnumFromTo e1 e2) =
>   liftM (apply prelEnumFromTo) (mapM (desugarExpr p) [e1,e2])
> desugarExpr p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply prelEnumFromThenTo) (mapM (desugarExpr p) [e1,e2,e3])
> desugarExpr p (UnaryMinus op e) =
>   liftM (Apply (unaryMinus op (typeOf e))) (desugarExpr p e)
>   where unaryMinus op ty
>           | op == minusId =
>               if ty == floatType then prelNegateFloat else prelNegate
>           | op == fminusId = prelNegateFloat
>           | otherwise = internalError "unaryMinus"
> desugarExpr p (Apply e1 e2) =
>   liftM2 Apply (desugarExpr p e1) (desugarExpr p e2)
> desugarExpr p (InfixApply e1 op e2) =
>   do
>     op' <- desugarExpr p (infixOp op)
>     e1' <- desugarExpr p e1
>     e2' <- desugarExpr p e2
>     return (Apply (Apply op' e1') e2')
> desugarExpr p (LeftSection e op) =
>   do
>     op' <- desugarExpr p (infixOp op)
>     e' <- desugarExpr p e
>     return (Apply op' e')
> desugarExpr p (RightSection op e) =
>   do
>     op' <- desugarExpr p (infixOp op)
>     e' <- desugarExpr p e
>     return (Apply (Apply (prelFlip ty1 ty2 ty3) op') e')
>   where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
> desugarExpr _ (Lambda p ts e) =
>   liftM2 (Lambda p) (mapM desugarTerm ts) (desugarExpr p e)
> desugarExpr p (Let ds e) = liftM2 Let (desugarDeclGroup ds) (desugarExpr p e)
> desugarExpr p (Do sts e) = desugarExpr p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' =
>           apply (prelBind_ (ioResType (typeOf e)) (ioResType (typeOf e')))
>                 [e,e']
>         desugarStmt (StmtBind p t e) e' =
>           apply (prelBind (typeOf t) (ioResType (typeOf e')))
>                 [e,Lambda p [t] e']
>         desugarStmt (StmtDecl ds) e' = mkLet ds e'
> desugarExpr p (IfThenElse e1 e2 e3) =
>   liftM3 mkCase (desugarExpr p e1) (desugarExpr p e2) (desugarExpr p e3)
>   where mkCase e1 e2 e3 =
>           Case e1 [caseAlt p truePattern e2,caseAlt p falsePattern e3]
> desugarExpr p (Case e as) = liftM2 Case (desugarExpr p e) (mapM desugarAlt as)
> desugarExpr p (Fcase e as) =
>   liftM2 Fcase (desugarExpr p e) (mapM desugarAlt as)

> desugarAlt :: Alt Type -> DesugarState (Alt Type)
> desugarAlt (Alt p t rhs) = liftM2 (Alt p) (desugarTerm t) (desugarRhs rhs)

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

> desugarListCompr :: Expression Type -> [Statement Type] -> Expression Type
>                  -> DesugarState (Expression Type)
> desugarListCompr e [] z =
>   return (apply (Constructor (consType (typeOf e)) qConsId) [e,z])
> desugarListCompr e (q:qs) z =
>   desugarQual q z >>= \(y,f) -> desugarListCompr e qs y >>= return . f

> desugarQual :: Statement Type -> Expression Type
>             -> DesugarState (Expression Type,
>                              Expression Type -> Expression Type)
> desugarQual (StmtExpr b) z = return (z,\e -> IfThenElse b e z)
> desugarQual (StmtBind p t l) z =
>   do
>     v <- freshVar "_#var" (typeOf t)
>     y <- freshVar "_#var" (typeOf z)
>     return (uncurry mkVar y,
>             \e -> apply (prelFoldr (fst v) (fst y)) [foldFunct v y e,z,l])
>   where foldFunct v l e =
>           Lambda p [uncurry VariablePattern v,uncurry VariablePattern l]
>             (Case (uncurry mkVar v)
>                   [caseAlt p t e,
>                    caseAlt p (uncurry VariablePattern v) (uncurry mkVar l)])
> desugarQual (StmtDecl ds) z = return (z,Let ds)

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: String -> Type -> DesugarState (Type,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM (mkName prefix) (updateSt (1 +))
>     return (ty,v)
>   where mkName pre n = renameIdent (mkIdent (pre ++ show n)) n

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
