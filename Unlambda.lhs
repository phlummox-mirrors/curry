% -*- LaTeX -*-
% $Id: Unlambda.lhs 2404 2007-07-20 14:39:32Z wlux $
%
% Copyright (c) 2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Unlambda.lhs}
\section{Naming lambda abstractions}
After simplification and before lifting functions to the top-level,
the compiler assigns explicit names to all lambda abstractions. Each
lambda abstraction $\lambda t_1 \dots t_n \rightarrow e$, which is
still present in the source code, is converted into a let expression
of the form \texttt{let $f\,t_1 \dots t_n = e$ in $f$}, where $f$ is
the canonical name of the lambda expression, and the type of the
lambda abstraction is recorded in the type environment.
\begin{verbatim}

> module Unlambda(unlambda) where
> import Base
> import Combined
> import Monad
> import TopEnv
> import Typing

> type UnlambdaState a = StateT ValueEnv Id a

> unlambda :: ValueEnv -> Module -> (Module,ValueEnv)
> unlambda tyEnv (Module m es is ds) = runSt doUnlambda tyEnv
>   where nEnv = newtypeEnv tyEnv
>         doUnlambda =
>           do
>             ds' <- nameLambdas m nEnv ds
>             tyEnv' <- fetchSt
>             return (Module m es is ds',tyEnv')

> class SyntaxTree a where
>   nameLambdas :: ModuleIdent -> NewtypeEnv -> a -> UnlambdaState a

> instance SyntaxTree a => SyntaxTree [a] where
>   nameLambdas m nEnv = mapM (nameLambdas m nEnv)

> instance SyntaxTree TopDecl where
>   nameLambdas m nEnv (BlockDecl d) = liftM BlockDecl (nameLambdas m nEnv d)
>   nameLambdas _ _ d = return d

> instance SyntaxTree Decl where
>   nameLambdas m nEnv (FunctionDecl p f eqs) =
>     liftM (FunctionDecl p f) (nameLambdas m nEnv eqs)
>   nameLambdas m nEnv (PatternDecl p t rhs) =
>     liftM (PatternDecl p t) (nameLambdas m nEnv rhs)
>   nameLambdas _ _ d = return d

> instance SyntaxTree Equation where
>   nameLambdas m nEnv (Equation p lhs rhs) =
>     liftM (Equation p lhs) (nameLambdas m nEnv rhs)

> instance SyntaxTree Rhs where
>   nameLambdas m nEnv (SimpleRhs p e _) =
>     liftM (flip (SimpleRhs p) []) (nameLambdas m nEnv e)

> instance SyntaxTree Expression where
>   nameLambdas _ _ (Literal l) = return (Literal l)
>   nameLambdas _ _ (Variable v) = return (Variable v)
>   nameLambdas _ _ (Constructor c) = return (Constructor c)
>   nameLambdas m nEnv (Apply e1 e2) =
>     liftM2 Apply (nameLambdas m nEnv e1) (nameLambdas m nEnv e2)
>   nameLambdas m nEnv (Lambda p ts e) =
>     do
>       updateSt_ (bindLambda m f (length ts) (Lambda p ts e))
>       nameLambdas m nEnv (Let [funDecl p f ts e] (mkVar f))
>     where f = lambdaId p
>           bindLambda m f n e tyEnv
>             | null (lookupTopEnv f tyEnv) = bindFun m f n (polyType ty) tyEnv
>             | otherwise = tyEnv
>             where ty = typeOf' nEnv tyEnv e
>   nameLambdas m nEnv (Let ds e) =
>     liftM2 Let (nameLambdas m nEnv ds) (nameLambdas m nEnv e)
>   nameLambdas m nEnv (Case e as) =
>     liftM2 Case (nameLambdas m nEnv e) (nameLambdas m nEnv as)

> instance SyntaxTree Alt where
>   nameLambdas m nEnv (Alt p t rhs) = liftM (Alt p t) (nameLambdas m nEnv rhs)

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> funDecl :: Position -> Ident -> [ConstrTerm] -> Expression -> Decl
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

\end{verbatim}