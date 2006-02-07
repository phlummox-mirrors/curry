% -*- LaTeX -*-
% $Id: Eval.lhs 1850 2006-02-07 14:19:24Z wlux $
%
% Copyright (c) 2001-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Eval.lhs}
\section{Collecting Evaluation Annotations}
The module \texttt{Eval} computes the evaluation annotation
environment. There is no need to check the annotations because this
happens already while checking the definitions of the module.
\begin{verbatim}

> module Eval(evalEnv,evalEnvGoal) where
> import Base
> import Env

\end{verbatim}
The function \texttt{evalEnv} collects all evaluation annotations of
the module by traversing the syntax tree.
\begin{verbatim}

> evalEnv :: [TopDecl] -> EvalEnv
> evalEnv ds = evals [d | BlockDecl d <- ds] emptyEnv

> evalEnvGoal :: Goal -> EvalEnv
> evalEnvGoal (Goal _ e ds) = evals e (evals ds emptyEnv)

> class SyntaxTree a where
>   evals :: a -> EvalEnv -> EvalEnv

> instance SyntaxTree a => SyntaxTree [a] where
>   evals xs env = foldr evals env xs

> instance SyntaxTree Decl where
>   evals (EvalAnnot _ fs ev) env = foldr (flip bindEnv ev) env fs
>   evals (FunctionDecl _ _ eqs) env = evals eqs env
>   evals (PatternDecl _ _ rhs) env = evals rhs env
>   evals _ env = env

> instance SyntaxTree Equation where
>   evals (Equation _ _ rhs) = evals rhs

> instance SyntaxTree Rhs where
>   evals (SimpleRhs _ e ds) = evals e . evals ds
>   evals (GuardedRhs es ds) = evals es . evals ds

> instance SyntaxTree CondExpr where
>   evals (CondExpr _ g e) = evals g . evals e

> instance SyntaxTree Expression where
>   evals (Literal _) = id
>   evals (Variable _) = id
>   evals (Constructor _) = id
>   evals (Paren e) = evals e
>   evals (Typed e _) = evals e
>   evals (Tuple es) = evals es
>   evals (List es) = evals es
>   evals (ListCompr e qs) = evals e . evals qs
>   evals (EnumFrom e) = evals e
>   evals (EnumFromThen e1 e2) = evals e1 . evals e2
>   evals (EnumFromTo e1 e2) = evals e1 . evals e2
>   evals (EnumFromThenTo e1 e2 e3) = evals e1 . evals e2 . evals e3
>   evals (UnaryMinus _ e) = evals e
>   evals (Apply e1 e2) = evals e1 . evals e2
>   evals (InfixApply e1 _ e2) = evals e1 . evals e2
>   evals (LeftSection e _) = evals e
>   evals (RightSection _ e) = evals e
>   evals (Lambda _ e) = evals e
>   evals (Let ds e) = evals ds . evals e
>   evals (Do sts e) = evals sts . evals e
>   evals (IfThenElse e1 e2 e3) = evals e1 . evals e2 . evals e3
>   evals (Case e as) = evals e . evals as

> instance SyntaxTree Statement where
>   evals (StmtExpr e) = evals e
>   evals (StmtDecl ds) = evals ds
>   evals (StmtBind _ e) = evals e

> instance SyntaxTree Alt where
>   evals (Alt _ _ rhs) = evals rhs

\end{verbatim}
