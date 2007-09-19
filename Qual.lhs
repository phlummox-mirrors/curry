% -*- LaTeX -*-
% $Id: Qual.lhs 2472 2007-09-19 14:55:02Z wlux $
%
% Copyright (c) 2001-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Qual.lhs}
\section{Proper Qualification}
After checking the module and before starting the translation into the
intermediate language, the compiler properly qualifies all
constructors and (global) functions occurring in a pattern or
expression such that their module prefix matches the module of their
definition. This is done also for functions and constructors declared
in the current module. Only functions and variables declared in local
declaration groups as well as function arguments remain unchanged.
\begin{verbatim}

> module Qual(Qual(..)) where
> import Base
> import Curry
> import TopEnv
> import ValueInfo

> class Qual a where
>   qual :: ValueEnv -> a -> a

> instance Qual a => Qual [a] where
>   qual tyEnv = map (qual tyEnv)

> instance Qual (Goal a) where
>   qual tyEnv (Goal p e ds) = Goal p (qual tyEnv e) (qual tyEnv ds)

> instance Qual (TopDecl a) where
>   qual tyEnv (BlockDecl d) = BlockDecl (qual tyEnv d)
>   qual _ d = d

> instance Qual (Decl a) where
>   qual tyEnv (FunctionDecl p f eqs) = FunctionDecl p f (qual tyEnv eqs)
>   qual tyEnv (PatternDecl p t rhs) =
>     PatternDecl p (qual tyEnv t) (qual tyEnv rhs)
>   qual _ d = d

> instance Qual (Equation a) where
>   qual tyEnv (Equation p lhs rhs) =
>     Equation p (qual tyEnv lhs) (qual tyEnv rhs)

> instance Qual (Lhs a) where
>   qual tyEnv (FunLhs f ts) = FunLhs f (qual tyEnv ts)
>   qual tyEnv (OpLhs t1 op t2) = OpLhs (qual tyEnv t1) op (qual tyEnv t2)
>   qual tyEnv (ApLhs lhs ts) = ApLhs (qual tyEnv lhs) (qual tyEnv ts)

> instance Qual (ConstrTerm a) where
>   qual _ (LiteralPattern a l) = LiteralPattern a l
>   qual _ (NegativePattern a op l) = NegativePattern a op l
>   qual _ (VariablePattern a v) = VariablePattern a v
>   qual tyEnv (ConstructorPattern a c ts) =
>     ConstructorPattern a (qual tyEnv c) (qual tyEnv ts)
>   qual tyEnv (InfixPattern a t1 op t2) =
>     InfixPattern a (qual tyEnv t1) (qual tyEnv op) (qual tyEnv t2)
>   qual tyEnv (ParenPattern t) = ParenPattern (qual tyEnv t)
>   qual tyEnv (TuplePattern ts) = TuplePattern (qual tyEnv ts)
>   qual tyEnv (ListPattern a ts) = ListPattern a (qual tyEnv ts)
>   qual tyEnv (AsPattern v t) = AsPattern v (qual tyEnv t)
>   qual tyEnv (LazyPattern t) = LazyPattern (qual tyEnv t)

> instance Qual (Rhs a) where
>   qual tyEnv (SimpleRhs p e ds) = SimpleRhs p (qual tyEnv e) (qual tyEnv ds) 
>   qual tyEnv (GuardedRhs es ds) = GuardedRhs (qual tyEnv es) (qual tyEnv ds)

> instance Qual (CondExpr a) where
>   qual tyEnv (CondExpr p g e) = CondExpr p (qual tyEnv g) (qual tyEnv e)

> instance Qual (Expression a) where
>   qual _ (Literal a l) = Literal a l
>   qual tyEnv (Variable a v) = Variable a (qual tyEnv v)
>   qual tyEnv (Constructor a c) = Constructor a (qual tyEnv c)
>   qual tyEnv (Paren e) = Paren (qual tyEnv e)
>   qual tyEnv (Typed e ty) = Typed (qual tyEnv e) ty
>   qual tyEnv (Tuple es) = Tuple (qual tyEnv es)
>   qual tyEnv (List a es) = List a (qual tyEnv es)
>   qual tyEnv (ListCompr e qs) = ListCompr (qual tyEnv e) (qual tyEnv qs)
>   qual tyEnv (EnumFrom e) = EnumFrom (qual tyEnv e)
>   qual tyEnv (EnumFromThen e1 e2) =
>     EnumFromThen (qual tyEnv e1) (qual tyEnv e2)
>   qual tyEnv (EnumFromTo e1 e2) = EnumFromTo (qual tyEnv e1) (qual tyEnv e2)
>   qual tyEnv (EnumFromThenTo e1 e2 e3) =
>     EnumFromThenTo (qual tyEnv e1) (qual tyEnv e2) (qual tyEnv e3)
>   qual tyEnv (UnaryMinus op e) = UnaryMinus op (qual tyEnv e)
>   qual tyEnv (Apply e1 e2) = Apply (qual tyEnv e1) (qual tyEnv e2)
>   qual tyEnv (InfixApply e1 op e2) =
>     InfixApply (qual tyEnv e1) (qual tyEnv op) (qual tyEnv e2)
>   qual tyEnv (LeftSection e op) = LeftSection (qual tyEnv e) (qual tyEnv op)
>   qual tyEnv (RightSection op e) = RightSection (qual tyEnv op) (qual tyEnv e)
>   qual tyEnv (Lambda p ts e) = Lambda p (qual tyEnv ts) (qual tyEnv e)
>   qual tyEnv (Let ds e) = Let (qual tyEnv ds) (qual tyEnv e)
>   qual tyEnv (Do sts e) = Do (qual tyEnv sts) (qual tyEnv e)
>   qual tyEnv (IfThenElse e1 e2 e3) =
>     IfThenElse (qual tyEnv e1) (qual tyEnv e2) (qual tyEnv e3)
>   qual tyEnv (Case e alts) = Case (qual tyEnv e) (qual tyEnv alts)

> instance Qual (Statement a) where
>   qual tyEnv (StmtExpr e) = StmtExpr (qual tyEnv e)
>   qual tyEnv (StmtBind p t e) = StmtBind p (qual tyEnv t) (qual tyEnv e)
>   qual tyEnv (StmtDecl ds) = StmtDecl (qual tyEnv ds)

> instance Qual (Alt a) where
>   qual tyEnv (Alt p t rhs) = Alt p (qual tyEnv t) (qual tyEnv rhs)

> instance Qual (InfixOp a) where
>   qual tyEnv (InfixOp a op) = InfixOp a (qual tyEnv op)
>   qual tyEnv (InfixConstr a op) = InfixConstr a (qual tyEnv op)

> instance Qual QualIdent where
>   qual tyEnv x
>     | isRenamed (unqualify x) = x
>     | otherwise =
>         case qualLookupTopEnv x tyEnv of
>           [y] -> origName y
>           _ -> internalError ("qual: " ++ show x)

\end{verbatim}
