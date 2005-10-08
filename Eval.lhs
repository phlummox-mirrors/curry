% -*- LaTeX -*-
% $Id: Eval.lhs 1789 2005-10-08 17:17:49Z wlux $
%
% Copyright (c) 2001-2005, Wolfgang Lux
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
> evalEnv ds = foldr collectAnnotsDecl emptyEnv [d | BlockDecl d <- ds]

> evalEnvGoal :: Goal -> EvalEnv
> evalEnvGoal (Goal _ e ds) =
>   collectAnnotsExpr e (foldr collectAnnotsDecl emptyEnv ds)

> collectAnnotsDecl :: Decl -> EvalEnv -> EvalEnv
> collectAnnotsDecl (EvalAnnot _ fs ev) env = foldr (flip bindEnv ev) env fs
> collectAnnotsDecl (FunctionDecl _ _ eqs) env = foldr collectAnnotsEqn env eqs
> collectAnnotsDecl (PatternDecl _ _ rhs) env = collectAnnotsRhs rhs env
> collectAnnotsDecl _ env = env

> collectAnnotsEqn :: Equation -> EvalEnv -> EvalEnv
> collectAnnotsEqn (Equation _ _ rhs) env = collectAnnotsRhs rhs env

> collectAnnotsRhs :: Rhs -> EvalEnv -> EvalEnv
> collectAnnotsRhs (SimpleRhs _ e ds) env =
>   collectAnnotsExpr e (foldr collectAnnotsDecl env ds)
> collectAnnotsRhs (GuardedRhs es ds) env =
>   foldr collectAnnotsCondExpr (foldr collectAnnotsDecl env ds) es

> collectAnnotsCondExpr :: CondExpr -> EvalEnv -> EvalEnv
> collectAnnotsCondExpr (CondExpr _ g e) env =
>   collectAnnotsExpr g (collectAnnotsExpr e env)

> collectAnnotsExpr :: Expression -> EvalEnv -> EvalEnv
> collectAnnotsExpr (Literal _) env = env
> collectAnnotsExpr (Variable _) env = env
> collectAnnotsExpr (Constructor _) env = env
> collectAnnotsExpr (Paren e) env = collectAnnotsExpr e env
> collectAnnotsExpr (Typed e _) env = collectAnnotsExpr e env
> collectAnnotsExpr (Tuple es) env = foldr collectAnnotsExpr env es
> collectAnnotsExpr (List es) env = foldr collectAnnotsExpr env es
> collectAnnotsExpr (ListCompr e qs) env =
>   collectAnnotsExpr e (foldr collectAnnotsStmt env qs)
> collectAnnotsExpr (EnumFrom e) env = collectAnnotsExpr e env
> collectAnnotsExpr (EnumFromThen e1 e2) env =
>   collectAnnotsExpr e1 (collectAnnotsExpr e2 env)
> collectAnnotsExpr (EnumFromTo e1 e2) env =
>   collectAnnotsExpr e1 (collectAnnotsExpr e2 env)
> collectAnnotsExpr (EnumFromThenTo e1 e2 e3) env =
>   collectAnnotsExpr e1 (collectAnnotsExpr e2 (collectAnnotsExpr e3 env))
> collectAnnotsExpr (UnaryMinus _ e) env = collectAnnotsExpr e env
> collectAnnotsExpr (Apply e1 e2) env =
>   collectAnnotsExpr e1 (collectAnnotsExpr e2 env)
> collectAnnotsExpr (InfixApply e1 _ e2) env =
>   collectAnnotsExpr e1 (collectAnnotsExpr e2 env)
> collectAnnotsExpr (LeftSection e _) env = collectAnnotsExpr e env
> collectAnnotsExpr (RightSection _ e) env = collectAnnotsExpr e env
> collectAnnotsExpr (Lambda _ e) env = collectAnnotsExpr e env
> collectAnnotsExpr (Let ds e) env =
>   foldr collectAnnotsDecl (collectAnnotsExpr e env) ds
> collectAnnotsExpr (Do sts e) env =
>   foldr collectAnnotsStmt (collectAnnotsExpr e env) sts
> collectAnnotsExpr (IfThenElse e1 e2 e3) env =
>   collectAnnotsExpr e1 (collectAnnotsExpr e2 (collectAnnotsExpr e3 env))
> collectAnnotsExpr (Case e alts) env =
>   collectAnnotsExpr e (foldr collectAnnotsAlt env alts)

> collectAnnotsStmt :: Statement -> EvalEnv -> EvalEnv
> collectAnnotsStmt (StmtExpr e) env = collectAnnotsExpr e env
> collectAnnotsStmt (StmtDecl ds) env = foldr collectAnnotsDecl env ds
> collectAnnotsStmt (StmtBind _ e) env = collectAnnotsExpr e env

> collectAnnotsAlt :: Alt -> EvalEnv -> EvalEnv
> collectAnnotsAlt (Alt _ _ rhs) env = collectAnnotsRhs rhs env

\end{verbatim}
