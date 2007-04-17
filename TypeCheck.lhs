% -*- LaTeX -*-
% $Id: TypeCheck.lhs 2154 2007-04-17 15:30:43Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeCheck.lhs}
\section{Type Inference}
This module implements the type checker of the Curry compiler. The
type checker is invoked after the syntactic correctness of the program
has been verified and kind checking has been applied to all type
expressions. Local variables have been renamed already. Therefore, the
compiler can maintain a flat type environment (which is necessary in
order to pass the type information to later phases of the compiler).
The type checker now checks the correct typing of all expressions and
also verifies that the type signatures given by the user match the
inferred types. The type checker uses algorithm
W~\cite{DamasMilner82:Principal} for inferring the types of
unannotated declarations, but allows for polymorphic recursion when a
type annotation is present.
\begin{verbatim}

> module TypeCheck(typeCheck,typeCheckGoal) where
> import Base
> import Pretty
> import CurryPP
> import Env
> import TopEnv
> import TypeSubst
> import TypeTrans
> import Combined
> import Error
> import List
> import Monad
> import SCC
> import Set
> import Utils

> infixl 5 $-$

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

\end{verbatim}
Before checking the function declarations of a module, the compiler
adds the types of all data and newtype constructors defined in the
current module to the type environment.
\begin{verbatim}

> typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> [TopDecl] -> Error ValueEnv
> typeCheck m tcEnv tyEnv ds =
>   run (tcDecls m tcEnv [d | BlockDecl d <- vds] >>
>        liftSt fetchSt >>= \theta -> liftM (subst theta) fetchSt)
>       (foldr (bindConstrs m tcEnv) tyEnv tds)
>   where (tds,vds) = partition isTypeDecl ds

\end{verbatim}
Type checking of a goal is simpler because there are no type
declarations.
\begin{verbatim}

> typeCheckGoal :: ModuleIdent -> TCEnv -> ValueEnv -> Goal -> Error ValueEnv
> typeCheckGoal m tcEnv tyEnv (Goal p e ds) =
>   run (tcRhs m tcEnv (SimpleRhs p e ds) >>=
>        checkSkolems p tcEnv (text "Goal:" <+> ppExpr 0 e) zeroSet >>
>        liftSt fetchSt >>= \theta -> liftM (subst theta) fetchSt)
>       tyEnv

\end{verbatim}
The type checker makes use of nested state monads in order to maintain
the type environment, the current substitution, and a counter, which
is used for generating fresh type variables.
\begin{verbatim}

> type TcState a = StateT ValueEnv (StateT TypeSubst (StateT Int Error)) a

> run :: TcState a -> ValueEnv -> Error a
> run m tyEnv = callSt (callSt (callSt m tyEnv) idSubst) 1

\end{verbatim}
\paragraph{Defining Data Constructors}
First, the types of all data and newtype constructors are entered into
the type environment. All type synonyms occurring in their types are
expanded. We cannot use \texttt{expandPolyType} for expanding the type
of a data or newtype constructor in function \texttt{bindConstr}
because of the different normalization scheme used for constructor
types and also because the name of the type could be ambiguous.
\begin{verbatim}

> bindConstrs :: ModuleIdent -> TCEnv -> TopDecl -> ValueEnv -> ValueEnv
> bindConstrs m tcEnv (DataDecl _ tc tvs cs) tyEnv = foldr bind tyEnv cs
>   where ty0 = constrType m tc tvs
>         bind (ConstrDecl _ _ c tys) =
>           bindConstr DataConstructor m tcEnv tvs c tys ty0
>         bind (ConOpDecl _ _ ty1 op ty2) =
>           bindConstr DataConstructor m tcEnv tvs op [ty1,ty2] ty0
> bindConstrs m tcEnv (NewtypeDecl _ tc tvs nc) tyEnv = bind nc tyEnv
>   where ty0 = constrType m tc tvs
>         bind (NewConstrDecl _ c ty) =
>           bindConstr (const . NewtypeConstructor) m tcEnv tvs c [ty] ty0
> bindConstrs _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindConstrs _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: (QualIdent -> Int -> TypeScheme -> ValueInfo) -> ModuleIdent
>            -> TCEnv -> [Ident] -> Ident -> [TypeExpr] -> Type
>            -> ValueEnv -> ValueEnv
> bindConstr f m tcEnv tvs c tys ty0 =
>   globalBindTopEnv m c (f (qualifyWith m c) (length tys) ty')
>   where ty' = polyType (normalize (length tvs) (foldr TypeArrow ty0 tys'))
>         tys' = expandMonoTypes tcEnv tvs tys

> constrType :: ModuleIdent -> Ident -> [Ident] -> Type
> constrType m tc tvs =
>   TypeConstructor (qualifyWith m tc) (map TypeVariable [0..length tvs-1])

\end{verbatim}
\paragraph{Type Signatures}
The type checker collects type signatures in a flat environment. The
types are not expanded so that the signatures can be used in the error
messages which are printed when an inferred type is less general than
the signature.
\begin{verbatim}

> type SigEnv = Env Ident TypeExpr

> noSigs :: SigEnv
> noSigs = emptyEnv

> bindTypeSigs :: Decl -> SigEnv -> SigEnv
> bindTypeSigs (TypeSig _ vs ty) env = foldr (flip bindEnv ty) env vs 
> bindTypeSigs _ env = env
        
\end{verbatim}
\paragraph{Type Inference}
Before type checking a group of declarations, a dependency analysis is
performed and the declaration group is split into minimal, nested
binding groups which are checked separately. Within each binding
group, first the type environment is extended with new bindings for
all variables and functions defined in the group. Next, each
declaration is checked in the extended type environment. Finally, the
types of all defined functions are generalized. The generalization
step will also check that the type signatures given by the user match
the inferred types.

The presence of unbound logical variables necessitates a monomorphism
restriction that prohibits unsound functions like
\begin{verbatim}
  bug = x =:= 1 & x =:= 'a' where x free
\end{verbatim}
This declaration would be accepted by the type checker if \verb|x|'s
type were generalized to $\forall\alpha.\alpha$. Curry's type system
(cf.\ Sect.~4.2 of~\cite{Hanus:Report}) is presently defined for
programs that have been transformed into a set of global, possibly
mutually recursive function declarations, where local declarations are
used only to introduce logical variables. Under this transformation,
the types of all local variables are monomorphic because the
Hindley-Milner type system does not generalize the types of
lambda-bound variables and logical variables are required to be
monomorphic by the existential rule of Curry's type system.

While sound, Curry's present type system is overly restrictive. Some
perfectly valid declarations like
\begin{verbatim}
  ok = (1:nil, 'a':nil) where nil = []
\end{verbatim}
are rejected by the compiler. A safe extension of Curry's type system
would allow polymorphic generalization for variables that are bound to
expressions containing no free variables. Yet, identifying ground
terms in general requires a complex semantic analysis and therefore
should not be a prerequisite for type checking. A good compromise is
to allow polymorphic generalization for variables that are bound to
expressions for which the compiler can easily prove that they do not
contain free variables. The distinction between expansive and
non-expansive expressions comes to help here, which is used by ML-like
languages in order to ensure type soundness in the presence of
imperative effects~\cite{WrightFelleisen94:TypeSoundness}. In Curry, a
non-expansive expression is either
\begin{itemize}\label{non-expansive}
\item a literal,
\item a variable,
\item an application of a constructor with arity $n$ to at most $n$
  non-expansive expressions,
\item an application of a function with arity $n$ to at most $n-1$
  non-expansive expressions, or
\item a let expression whose body is a non-expansive expression and
  whose local declarations are either function declarations or
  variable declarations of the form \texttt{$x$=$e$} where $e$ is a
  non-expansive expression, or
\item an expression whose desugared form is one of the above.
\end{itemize}
At first it may seem strange that variables are included in the list
above because a variable may be bound to a logical variable. However,
this is no problem because type variables that are present among the
typing assumptions of the environment enclosing a let expression
cannot be generalized.

Recently, Garrigue has shown that ML's value restriction can be lifted
a bit and that generalizing type variables that appear only in
covariant positions is sound~\cite{Garrigue04:ValueRestriction}.
Obviously, this generalization does not hold for Curry with
\texttt{let x = unknown in x} being the canonical counter-example.

Within a group of mutually recursive declarations, all type variables
that appear in the types of the variables defined in the group must
not be generalized. Without this restriction, the compiler would
accept the function
\begin{verbatim}
  illTyped = x=:=1 &> f True "Hello"
    where (x:xs) = f True (repeat unknown)
          f _ [] = []
          f b (y:ys) = (if b then y else x) : f (not b) ys
\end{verbatim}
whose result is the ill-typed list \verb|['H',1,'l',1,'o']|,
because \verb|f|'s type would incorrectly be generalized to
$\forall\alpha.\texttt{Bool}\rightarrow[\alpha]\rightarrow[\alpha]$.
\begin{verbatim}

> tcDecls :: ModuleIdent -> TCEnv -> [Decl] -> TcState ()
> tcDecls m tcEnv ds =
>   mapM_ (tcDeclGroup m tcEnv (foldr bindTypeSigs noSigs ods))
>         (scc bv (qfv m) vds)
>   where (vds,ods) = partition isValueDecl ds

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> [Decl] -> TcState ()
> tcDeclGroup m tcEnv _ [ForeignDecl p cc _ ie f ty] =
>   tcForeignFunct m tcEnv p cc ie f ty
> tcDeclGroup m tcEnv sigs [FreeDecl p vs] = bindDeclVars m tcEnv sigs p vs
> tcDeclGroup m tcEnv sigs ds =
>   do
>     tyEnv0 <- fetchSt
>     mapM_ (bindDecl m tcEnv sigs) ds
>     tys <- mapM (tcDecl m tcEnv) ds
>     tyEnv <- fetchSt
>     theta <- liftSt fetchSt
>     let vs = [v | PatternDecl _ t rhs <- ds,
>                   not (isVariablePattern t || isNonExpansive tcEnv tyEnv rhs),
>                   v <- bv t]
>         tvss = map (typeVars . subst theta . flip varType tyEnv) vs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) (concat tvss)
>     zipWithM_ (genDecl m tcEnv tyEnv sigs fvs . subst theta) tys ds

> bindDecl :: ModuleIdent -> TCEnv -> SigEnv -> Decl -> TcState ()
> bindDecl m tcEnv sigs (FunctionDecl p f eqs) =
>   case lookupEnv f sigs of
>     Just ty -> updateSt_ (bindFun m f n (expandPolyType tcEnv ty))
>     Nothing ->
>       replicateM (n + 1) freshTypeVar >>=
>       updateSt_ . bindFun m f n . monoType . foldr1 TypeArrow
>   where n = eqnArity (head eqs)
> bindDecl m tcEnv sigs (PatternDecl p t _) =
>   case t of
>     VariablePattern v -> bindDeclVar True m tcEnv sigs p v
>     _ -> bindDeclVars m tcEnv sigs p (bv t)

> bindDeclVars :: ModuleIdent -> TCEnv -> SigEnv -> Position -> [Ident]
>              -> TcState ()
> bindDeclVars m tcEnv sigs p = mapM_ (bindDeclVar False m tcEnv sigs p)

> bindDeclVar :: Bool -> ModuleIdent -> TCEnv -> SigEnv -> Position -> Ident
>             -> TcState ()
> bindDeclVar poly m tcEnv sigs p v =
>   case lookupEnv v sigs of
>     Just ty
>       | poly || null (fv ty) ->
>           updateSt_ (bindFun m v 0 (expandPolyType tcEnv ty))
>       | otherwise -> errorAt p (polymorphicVar v)
>     Nothing -> bindLambdaVar m v

> tcDecl :: ModuleIdent -> TCEnv -> Decl -> TcState Type
> tcDecl m tcEnv (FunctionDecl _ f eqs) =
>   do
>     tyEnv0 <- fetchSt
>     theta <- liftSt fetchSt
>     ty <- inst (varType f tyEnv0)
>     mapM_ (tcEquation m tcEnv (fsEnv (subst theta tyEnv0)) ty) eqs
>     return ty
> tcDecl m tcEnv (PatternDecl p t rhs) =
>   do
>     ty <- tcConstrTerm m tcEnv p t
>     tcRhs m tcEnv rhs >>=
>       unify p "pattern binding" (ppConstrTerm 0 t) tcEnv ty
>     return ty

> tcEquation :: ModuleIdent -> TCEnv -> Set Int -> Type -> Equation
>            -> TcState ()
> tcEquation m tcEnv fs ty eq@(Equation p lhs rhs) =
>   do
>     tcEqn m tcEnv p ts rhs >>=
>       unify p "function declaration" (ppEquation eq) tcEnv ty
>     checkSkolems p tcEnv (text "Function:" <+> ppIdent f) fs ty
>   where (f,ts) = flatLhs lhs

> tcEqn :: ModuleIdent -> TCEnv -> Position -> [ConstrTerm] -> Rhs
>       -> TcState Type
> tcEqn m tcEnv p ts rhs =
>   do
>     bindLambdaVars m ts
>     tys <- mapM (tcConstrTerm m tcEnv p) ts
>     ty <- tcRhs m tcEnv rhs
>     return (foldr TypeArrow ty tys)

> bindLambdaVars :: QuantExpr t => ModuleIdent -> t -> TcState ()
> bindLambdaVars m t = mapM_ (bindLambdaVar m) (bv t)

> bindLambdaVar :: ModuleIdent -> Ident -> TcState ()
> bindLambdaVar m v = freshTypeVar >>= updateSt_ . bindFun m v 0 . monoType

\end{verbatim}
The code in \texttt{genDecl} below verifies that the inferred type of
a function matches its declared type. Since the type inferred for the
left hand side of a function or variable declaration is an instance of
its declared type -- provided a type signature is given -- it can only
be more specific. Therefore, if the inferred type does not match the
type signature, the declared type must be too general. No check is
necessary for the variables in variable and other pattern declarations
because the types of variables must be monomorphic, which is checked
in \texttt{bindDeclVar} above.
\begin{verbatim}

> genDecl :: ModuleIdent -> TCEnv -> ValueEnv -> SigEnv -> Set Int -> Type
>         -> Decl -> TcState ()
> genDecl m tcEnv _ sigs fvs ty (FunctionDecl p f eqs) =
>   case lookupEnv f sigs of
>     Just sigTy
>       | sigma == expandPolyType tcEnv sigTy -> return ()
>       | otherwise -> errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>     Nothing -> updateSt_ (rebindFun m f (eqnArity (head eqs)) sigma)
>   where what = text "Function:" <+> ppIdent f
>         sigma = gen fvs ty
> genDecl m tcEnv tyEnv sigs fvs ty (PatternDecl p t rhs) =
>   case t of
>     VariablePattern v ->
>       case lookupEnv v sigs of
>         Just sigTy
>           | sigma == expandPolyType tcEnv sigTy -> return ()
>           | otherwise -> errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>         Nothing
>           | poly -> updateSt_ (rebindFun m v 0 sigma)
>           | otherwise -> return ()
>       where what = text "Variable: " <+> ppIdent v
>             poly = isNonExpansive tcEnv tyEnv rhs
>             sigma = if poly then gen fvs ty else monoType ty
>     _ -> return ()

> class Binding a where
>   isNonExpansive :: TCEnv -> ValueEnv -> a -> Bool

> instance Binding a => Binding [a] where
>   isNonExpansive tcEnv tyEnv = all (isNonExpansive tcEnv tyEnv)

> instance Binding Decl where
>   isNonExpansive _ _ (InfixDecl _ _ _ _) = True
>   isNonExpansive _ _ (TypeSig _ _ _) = True
>   isNonExpansive _ _ (FunctionDecl _ _ (eq:eqs)) = eqnArity eq > 0
>   isNonExpansive tcEnv _ (ForeignDecl _ _ _ _ _ ty) =
>     foreignArity (expandPolyType tcEnv ty) > 0
>   isNonExpansive tcEnv tyEnv (PatternDecl _ t rhs) =
>     isVariablePattern t && isNonExpansive tcEnv tyEnv rhs
>   isNonExpansive _ _ (FreeDecl _ _) = False
>   isNonExpansive _ _ (TrustAnnot _ _ _) = True

> instance Binding Rhs where
>   isNonExpansive tcEnv tyEnv (SimpleRhs _ e ds) =
>     isNonExpansive tcEnv tyEnv ds && isNonExpansive tcEnv tyEnv e
>   isNonExpansive _ _ (GuardedRhs _ _) = False

> instance Binding Expression where
>   isNonExpansive tcEnv tyEnv = isNonExpansiveApp tcEnv tyEnv 0

> isNonExpansiveApp :: TCEnv -> ValueEnv -> Int -> Expression -> Bool
> isNonExpansiveApp _ _ _ (Literal _) = True
> isNonExpansiveApp _ tyEnv n (Variable v)
>   | isRenamed (unqualify v) = n == 0 || n < arity v tyEnv
>   | otherwise = n < arity v tyEnv
> isNonExpansiveApp _ _ _ (Constructor _) = True
> isNonExpansiveApp tcEnv tyEnv n (Paren e) =
>   isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv n (Typed e _) =
>   isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv _ (Tuple es) =
>   isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv _ (List es) =
>   isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv n (Apply f e) =
>   isNonExpansive tcEnv tyEnv e && isNonExpansiveApp tcEnv tyEnv (n + 1) f
> isNonExpansiveApp tcEnv tyEnv n (InfixApply e1 op e2) =
>   isNonExpansiveApp tcEnv tyEnv (n + 2) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e1 && isNonExpansive tcEnv tyEnv e2
> isNonExpansiveApp tcEnv tyEnv n (LeftSection e op) =
>   isNonExpansiveApp tcEnv tyEnv (n + 1) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e
> isNonExpansiveApp _ _ n (Lambda ts _) = n < length ts
> isNonExpansiveApp tcEnv tyEnv n (Let ds e) =
>   isNonExpansive tcEnv tyEnv ds && isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp _ _ _ _ = False

\end{verbatim}
Argument and result types of foreign functions using the
\texttt{ccall} calling convention are restricted to the basic types
\texttt{Bool}, \texttt{Char}, \texttt{Int}, \texttt{Float},
\texttt{Ptr}, \texttt{FunPtr}, and \texttt{StablePtr}. In addition,
$\texttt{IO}\;t$ is a legitimate result type when $t$ is either one of
the basic types or \texttt{()}. As an extension to the Haskell foreign
function interface specification~\cite{Chakravarty03:FFI}, the compiler
supports the non-standard \texttt{rawcall} calling convention, which
allows arbitrary argument and result types. However, in contrast
to the \texttt{ccall} calling convention, no marshaling takes place at
all even for the basic types (cf.\ Sect.~\ref{sec:il-compile} with
regard to marshalling). The type of a dynamic function wrapper is
restricted further to be of the form $\texttt{FunPtr}\;t \rightarrow
t$, where $t$ is a valid foreign function type, and the type of a
foreign address must be either $\texttt{Ptr}\;a$ or
$\texttt{FunPtr}\;a$, where $a$ is an arbitrary type.

Note that a foreign function with type $t_1 \rightarrow \dots
\rightarrow t_n \rightarrow t$ has arity $n$ unless the result type
$t$ is $\texttt{IO}\;t'$, in which case its arity will be $n+1$. This
special case reflects the fact that the type $\texttt{IO}\;t$ is
equivalent to $\emph{World}\rightarrow(t,\emph{World})$.
\begin{verbatim}

> tcForeignFunct :: ModuleIdent -> TCEnv -> Position -> CallConv
>                -> Maybe String -> Ident -> TypeExpr -> TcState ()
> tcForeignFunct m tcEnv p cc ie f ty =
>   do
>     checkForeignType cc (rawType ty')
>     updateSt_ (bindFun m f (foreignArity ty') ty')
>   where ty' = expandPolyType tcEnv ty
>         checkForeignType cc ty
>           | cc == CallConvPrimitive = return ()
>           | ie == Just "dynamic" = checkCDynCallType tcEnv p cc ty
>           | maybe False ('&' `elem`) ie = checkCAddrType tcEnv p ty
>           | otherwise = checkCCallType tcEnv p cc ty

> foreignArity :: TypeScheme -> Int
> foreignArity (ForAll _ ty)
>   | isIO (arrowBase ty') = length tys + 1
>   | otherwise = length tys
>   where (tys,ty') = arrowUnapply ty
>         isIO (TypeConstructor tc [_]) = tc == qIOId
>         isIO _ = False

> checkCCallType :: TCEnv -> Position -> CallConv -> Type -> TcState ()
> checkCCallType tcEnv p CallConvCCall (TypeArrow ty1 ty2)
>   | isCArgType ty1 = checkCCallType tcEnv p CallConvCCall ty2
>   | otherwise = errorAt p (invalidCType "argument" tcEnv ty1)
> checkCCallType tcEnv p CallConvCCall ty
>   | isCRetType ty = return ()
>   | otherwise = errorAt p (invalidCType "result" tcEnv ty)
> checkCCallType _ _ CallConvRawCall _ = return ()

> checkCDynCallType :: TCEnv -> Position -> CallConv -> Type -> TcState ()
> checkCDynCallType tcEnv p cc (TypeArrow (TypeConstructor tc [ty1]) ty2)
>   | tc == qFunPtrId && ty1 == ty2 = checkCCallType tcEnv p cc ty1
> checkCDynCallType tcEnv p _ ty =
>   errorAt p (invalidCType "dynamic function" tcEnv ty)

> checkCAddrType :: TCEnv -> Position -> Type -> TcState ()
> checkCAddrType tcEnv p ty
>   | isCPtrType ty = return ()
>   | otherwise = errorAt p (invalidCType "static address" tcEnv ty)

> isCArgType :: Type -> Bool
> isCArgType (TypeConstructor tc []) = tc `elem` cBasicTypeId
> isCArgType (TypeConstructor tc [_]) = tc `elem` qStablePtrId:cPointerTypeId
> isCArgType _ = False

> isCRetType :: Type -> Bool
> isCRetType (TypeConstructor tc [ty])
>   | tc == qIOId = ty == unitType || isCArgType ty
> isCRetType ty = isCArgType ty

> isCPtrType :: Type -> Bool
> isCPtrType (TypeConstructor tc [_]) = tc `elem` cPointerTypeId
> isCPtrType _ = False

> cBasicTypeId, cPointerTypeId :: [QualIdent]
> cBasicTypeId = [qBoolId,qCharId,qIntId,qFloatId]
> cPointerTypeId = [qPtrId,qFunPtrId]

\end{verbatim}
\paragraph{Patterns and Expressions}
\begin{verbatim}

> tcLiteral :: ModuleIdent -> Literal -> TcState Type
> tcLiteral _ (Char _) = return charType
> tcLiteral m (Int v _) =
>   do
>     ty <- freshConstrained [intType,floatType]
>     updateSt_ (bindFun m v 0 (monoType ty))
>     return ty
> tcLiteral _ (Float _) = return floatType
> tcLiteral _ (String _) = return stringType

> tcConstrTerm :: ModuleIdent -> TCEnv -> Position -> ConstrTerm -> TcState Type
> tcConstrTerm m _ _ (LiteralPattern l) = tcLiteral m l
> tcConstrTerm m _ _ (NegativePattern _ l) = tcLiteral m l
> tcConstrTerm _ _ _ (VariablePattern v) = fetchSt >>= inst . varType v
> tcConstrTerm m tcEnv p t@(ConstructorPattern c ts) =
>   tcConstrApp m tcEnv p (ppConstrTerm 0 t) c ts
> tcConstrTerm m tcEnv p t@(InfixPattern t1 op t2) =
>   tcConstrApp m tcEnv p (ppConstrTerm 0 t) op [t1,t2]
> tcConstrTerm m tcEnv p (ParenPattern t) = tcConstrTerm m tcEnv p t
> tcConstrTerm m tcEnv p (TuplePattern ts) =
>   liftM tupleType (mapM (tcConstrTerm m tcEnv p) ts)
> tcConstrTerm m tcEnv p t@(ListPattern ts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (tcElem (ppConstrTerm 0 t) ty) ts
>     return (listType ty)
>   where tcElem doc ty t =
>           tcConstrTerm m tcEnv p t >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 tcEnv ty
> tcConstrTerm m tcEnv p t@(AsPattern v t') =
>   do
>     ty <- tcConstrTerm m tcEnv p (VariablePattern v)
>     tcConstrTerm m tcEnv p t' >>=
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv ty
>     return ty
> tcConstrTerm m tcEnv p (LazyPattern t) = tcConstrTerm m tcEnv p t

> tcConstrApp :: ModuleIdent -> TCEnv -> Position -> Doc -> QualIdent
>             -> [ConstrTerm] -> TcState Type
> tcConstrApp m tcEnv p doc c ts =
>   do
>     tyEnv <- fetchSt
>     (tys,ty) <- liftM arrowUnapply (skol (conType c tyEnv))
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     zipWithM_ (tcConstrArg m tcEnv p doc) ts tys
>     return ty
>   where n = length ts

> tcConstrArg :: ModuleIdent -> TCEnv -> Position -> Doc -> ConstrTerm -> Type
>             -> TcState ()
> tcConstrArg m tcEnv p doc t ty =
>   tcConstrTerm m tcEnv p t >>=
>   unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv ty

> tcRhs :: ModuleIdent -> TCEnv -> Rhs -> TcState Type
> tcRhs m tcEnv (SimpleRhs p e ds) =
>   do
>     tcDecls m tcEnv ds
>     tcExpr m tcEnv p e
> tcRhs m tcEnv (GuardedRhs es ds) =
>   do
>     tcDecls m tcEnv ds
>     gty <- guardType es
>     ty <- freshTypeVar
>     mapM_ (tcCondExpr m tcEnv gty ty) es
>     return ty
>   where guardType es
>           | length es > 1 = return boolType
>           | otherwise = freshConstrained [successType,boolType]

> tcCondExpr :: ModuleIdent -> TCEnv -> Type -> Type -> CondExpr -> TcState ()
> tcCondExpr m tcEnv gty ty (CondExpr p g e) =
>   do
>     tcExpr m tcEnv p g >>= unify p "guard" (ppExpr 0 g) tcEnv gty
>     tcExpr m tcEnv p e >>= unify p "guarded expression" (ppExpr 0 e) tcEnv ty

> tcExpr :: ModuleIdent -> TCEnv -> Position -> Expression -> TcState Type
> tcExpr m _ _ (Literal l) = tcLiteral m l
> tcExpr m tcEnv p (Variable v) = fetchSt >>= inst . funType v
> tcExpr m tcEnv p (Constructor c) = fetchSt >>= inst . conType c
> tcExpr m tcEnv p (Typed e sig) =
>   do
>     tyEnv0 <- fetchSt
>     ty <- inst sigma'
>     tcExpr m tcEnv p e >>=
>       unify p "explicitly typed expression" (ppExpr 0 e) tcEnv ty
>     theta <- liftSt fetchSt
>     let sigma = gen (fvEnv (subst theta tyEnv0)) (subst theta ty)
>     unless (sigma == sigma')
>       (errorAt p (typeSigTooGeneral tcEnv (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return ty
>   where sigma' = expandPolyType tcEnv sig
> tcExpr m tcEnv p (Paren e) = tcExpr m tcEnv p e
> tcExpr m tcEnv p (Tuple es) = liftM tupleType (mapM (tcExpr m tcEnv p) es)
> tcExpr m tcEnv p e@(List es) =
>   do
>     ty <- freshTypeVar
>     mapM_ (tcElem (ppExpr 0 e) ty) es
>     return (listType ty)
>   where tcElem doc ty e =
>           tcExpr m tcEnv p e >>=
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e) tcEnv ty
> tcExpr m tcEnv p (ListCompr e qs) =
>   do
>     mapM_ (tcQual m tcEnv p) qs
>     liftM listType (tcExpr m tcEnv p e)
> tcExpr m tcEnv p e@(EnumFrom e1) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     return (listType intType)
> tcExpr m tcEnv p e@(EnumFromThen e1 e2) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     return (listType intType)
> tcExpr m tcEnv p e@(EnumFromTo e1 e2) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     return (listType intType)
> tcExpr m tcEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     tcExpr m tcEnv p e3 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) tcEnv intType
>     return (listType intType)
> tcExpr m tcEnv p e@(UnaryMinus op e1) =
>   do
>     ty <- opType op
>     tcExpr m tcEnv p e1 >>=
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv ty
>     return ty
>   where opType op
>           | op == minusId = freshConstrained [intType,floatType]
>           | op == fminusId = return floatType
>           | otherwise = internalError ("tcExpr unary " ++ name op)
> tcExpr m tcEnv p e@(Apply e1 e2) =
>   do
>     (alpha,beta) <-
>       tcExpr m tcEnv p e1 >>=
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>               tcEnv
>     tcExpr m tcEnv p e2 >>=
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             tcEnv alpha
>     return beta
> tcExpr m tcEnv p e@(InfixApply e1 op e2) =
>   do
>     (alpha,beta,gamma) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     tcExpr m tcEnv p e1 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv alpha
>     tcExpr m tcEnv p e2 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv beta
>     return gamma
> tcExpr m tcEnv p e@(LeftSection e1 op) =
>   do
>     (alpha,beta) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               tcEnv
>     tcExpr m tcEnv p e1 >>=
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv alpha
>     return beta
> tcExpr m tcEnv p e@(RightSection op e1) =
>   do
>     (alpha,beta,gamma) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     tcExpr m tcEnv p e1 >>=
>       unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv beta
>     return (TypeArrow alpha gamma)
> tcExpr m tcEnv p (Lambda ts e) =
>   do
>     bindLambdaVars m ts
>     tys <- mapM (tcConstrTerm m tcEnv p) ts
>     ty <- tcExpr m tcEnv p e
>     return (foldr TypeArrow ty tys)
> tcExpr m tcEnv p (Let ds e) =
>   do
>     tcDecls m tcEnv ds
>     tcExpr m tcEnv p e
> tcExpr m tcEnv p (Do sts e) =
>   do
>     mapM_ (tcStmt m tcEnv p) sts
>     ty <- liftM ioType freshTypeVar
>     tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) tcEnv ty
>     return ty
> tcExpr m tcEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv boolType
>     ty <- tcExpr m tcEnv p e2
>     tcExpr m tcEnv p e3 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>             tcEnv ty
>     return ty
> tcExpr m tcEnv p (Case e alts) =
>   do
>     tyLhs <- tcExpr m tcEnv p e
>     tyRhs <- freshTypeVar
>     mapM_ (tcAlt m tcEnv tyLhs tyRhs) alts
>     return tyRhs

> tcAlt :: ModuleIdent -> TCEnv -> Type -> Type -> Alt -> TcState ()
> tcAlt m tcEnv tyLhs tyRhs a@(Alt p t rhs) =
>   do
>     bindLambdaVars m t
>     tcConstrTerm m tcEnv p t >>=
>       unify p "case pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>             tcEnv tyLhs
>     tcRhs m tcEnv rhs >>= unify p "case branch" doc tcEnv tyRhs
>   where doc = ppAlt a

> tcQual :: ModuleIdent -> TCEnv -> Position -> Statement -> TcState ()
> tcQual m tcEnv p (StmtExpr e) =
>   tcExpr m tcEnv p e >>= unify p "guard" (ppExpr 0 e) tcEnv boolType
> tcQual m tcEnv p q@(StmtBind t e) =
>   do
>     bindLambdaVars m t
>     ty <- tcConstrTerm m tcEnv p t
>     tcExpr m tcEnv p e >>=
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (listType ty)
> tcQual m tcEnv p (StmtDecl ds) = tcDecls m tcEnv ds

> tcStmt :: ModuleIdent -> TCEnv -> Position -> Statement -> TcState ()
> tcStmt m tcEnv p (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     tcExpr m tcEnv p e >>=
>       unify p "statement" (ppExpr 0 e) tcEnv (ioType alpha)
> tcStmt m tcEnv p st@(StmtBind t e) =
>   do
>     bindLambdaVars m t
>     ty <- tcConstrTerm m tcEnv p t
>     tcExpr m tcEnv p e >>=
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (ioType ty)
> tcStmt m tcEnv p (StmtDecl ds) = tcDecls m tcEnv ds

\end{verbatim}
The function \texttt{tcArrow} checks that its argument can be used as
an arrow type $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$. Similarly, the function \texttt{tcBinary} checks
that its argument can be used as an arrow type
$\alpha\rightarrow\beta\rightarrow\gamma$ and returns the triple
$(\alpha,\beta,\gamma)$.
\begin{verbatim}

> tcArrow :: Position -> String -> Doc -> TCEnv -> Type
>         -> TcState (Type,Type)
> tcArrow p what doc tcEnv ty =
>   do
>     theta <- liftSt fetchSt
>     unaryArrow (subst theta ty)
>   where unaryArrow (TypeArrow ty1 ty2) = return (ty1,ty2)
>         unaryArrow (TypeVariable tv) =
>           do
>             alpha <- freshTypeVar
>             beta <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow alpha beta)))
>             return (alpha,beta)
>         unaryArrow ty = errorAt p (nonFunctionType what doc tcEnv ty)

> tcBinary :: Position -> String -> Doc -> TCEnv -> Type
>          -> TcState (Type,Type,Type)
> tcBinary p what doc tcEnv ty =
>   tcArrow p what doc tcEnv ty >>= uncurry binaryArrow
>   where binaryArrow ty1 (TypeArrow ty2 ty3) = return (ty1,ty2,ty3)
>         binaryArrow ty1 (TypeVariable tv) =
>           do
>             beta <- freshTypeVar
>             gamma <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow beta gamma)))
>             return (ty1,beta,gamma)
>         binaryArrow ty1 ty2 =
>           errorAt p (nonBinaryOp what doc tcEnv (TypeArrow ty1 ty2))

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> TCEnv -> Type -> Type
>       -> TcState ()
> unify p what doc tcEnv ty1 ty2 =
>   liftSt $ {-$-}
>   do
>     theta <- fetchSt
>     let ty1' = subst theta ty1
>     let ty2' = subst theta ty2
>     either (errorAt p . typeMismatch what doc tcEnv ty1' ty2')
>            (updateSt_ . compose)
>            (unifyTypes tcEnv ty1' ty2')

> unifyTypes :: TCEnv -> Type -> Type -> Either Doc TypeSubst
> unifyTypes _ (TypeVariable tv1) (TypeVariable tv2)
>   | tv1 == tv2 = Right idSubst
>   | otherwise = Right (bindSubst tv1 (TypeVariable tv2) idSubst)
> unifyTypes tcEnv (TypeVariable tv) ty
>   | tv `elem` typeVars ty = Left (recursiveType tcEnv tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes tcEnv ty (TypeVariable tv)
>   | tv `elem` typeVars ty = Left (recursiveType tcEnv tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes _ (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2)
>   | tv1 == tv2 = Right idSubst
>   | tys1 == tys2 = Right (bindSubst tv1 (TypeConstrained tys2 tv2) idSubst)
> unifyTypes tcEnv (TypeConstrained tys tv) ty =
>   foldr (choose . unifyTypes tcEnv ty)
>         (Left (incompatibleTypes tcEnv ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes tcEnv ty (TypeConstrained tys tv) =
>   foldr (choose . unifyTypes tcEnv ty)
>         (Left (incompatibleTypes tcEnv ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes tcEnv (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = unifyTypeLists tcEnv tys1 tys2
> unifyTypes tcEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   unifyTypeLists tcEnv [ty11,ty12] [ty21,ty22]
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Right idSubst
> unifyTypes tcEnv ty1 ty2 = Left (incompatibleTypes tcEnv ty1 ty2)

> unifyTypeLists :: TCEnv -> [Type] -> [Type] -> Either Doc TypeSubst
> unifyTypeLists _ [] _ = Right idSubst
> unifyTypeLists _ _ [] = Right idSubst
> unifyTypeLists tcEnv (ty1:tys1) (ty2:tys2) =
>   either Left (unifyTypesTheta tcEnv ty1 ty2) (unifyTypeLists tcEnv tys1 tys2)
>   where unifyTypesTheta tcEnv ty1 ty2 theta =
>           either Left (Right . flip compose theta)
>                  (unifyTypes tcEnv (subst theta ty1) (subst theta ty2))

\end{verbatim}
For each function declaration, the type checker ensures that no skolem
type escapes its scope. This is slightly more general than the
algorithm in~\cite{LauferOdersky94:AbstractTypes}, which checks for
escaping skolems at every let binding, but is still sound.
\begin{verbatim}

> checkSkolems :: Position -> TCEnv -> Doc -> Set Int -> Type -> TcState ()
> checkSkolems p tcEnv what fs ty =
>   do
>     ty' <- liftM (flip subst ty) (liftSt fetchSt)
>     unless (all (`elemSet` fs) (typeSkolems ty'))
>            (errorAt p (skolemEscapingScope tcEnv what ty'))

\end{verbatim}
\paragraph{Instantiation and Generalization}
We use negative offsets for fresh type variables.
\begin{verbatim}

> fresh :: (Int -> a) -> TcState a
> fresh f = liftM f (liftSt (liftSt (updateSt (1 +))))

> freshVar :: (Int -> a) -> TcState a
> freshVar f = fresh (\n -> f (- n))

> freshTypeVar :: TcState Type
> freshTypeVar = freshVar TypeVariable

> freshConstrained :: [Type] -> TcState Type
> freshConstrained tys = freshVar (TypeConstrained tys)

> freshSkolem :: TcState Type
> freshSkolem = fresh TypeSkolem

> inst :: TypeScheme -> TcState Type
> inst (ForAll n ty) =
>   do
>     tys <- replicateM n freshTypeVar
>     return (expandAliasType tys ty)

\end{verbatim}
The function \texttt{skol} instantiates the type of data and newtype
constructors in patterns. All universally quantified type variables
are instantiated with fresh type variables and all existentially
quantified type variables are instantiated with fresh skolem types.
\begin{verbatim}

> skol :: TypeScheme -> TcState Type
> skol (ForAll n ty) =
>   do
>     tys <- replicateM m freshTypeVar
>     tys' <- replicateM (n - m) freshSkolem
>     return (expandAliasType (tys ++ tys') ty)
>   where m = arity (arrowBase ty)
>         arity (TypeConstructor _ tys) = length tys

> gen :: Set Int -> Type -> TypeScheme
> gen gvs ty =
>   ForAll (length tvs) (subst (foldr2 bindSubst idSubst tvs tvs') ty)
>   where tvs = [tv | tv <- nub (typeVars ty), tv `notElemSet` gvs]
>         tvs' = map TypeVariable [0..]

> replicateM :: Monad m => Int -> m a -> m [a]
> replicateM n = sequence . replicate n

\end{verbatim}
\paragraph{Auxiliary Functions}
\begin{verbatim}

> isVariablePattern :: ConstrTerm -> Bool
> isVariablePattern (VariablePattern _) = True
> isVariablePattern _ = False

\end{verbatim}
The functions \texttt{fvEnv} and \texttt{fsEnv} compute the set of
free type variables and free skolems of a type environment,
respectively. We ignore the types of data and newtype constructors
here because we know that they are closed.
\begin{verbatim}

> fvEnv :: ValueEnv -> Set Int
> fvEnv tyEnv = fromListSet (concatMap typeVars (localTypes tyEnv))

> fsEnv :: ValueEnv -> Set Int
> fsEnv tyEnv = fromListSet (concatMap typeSkolems (localTypes tyEnv))

> localTypes :: ValueEnv -> [TypeScheme]
> localTypes tyEnv = [ty | (_,Value _ _ ty) <- localBindings tyEnv]

\end{verbatim}
Error functions.
\begin{verbatim}

> polymorphicVar :: Ident -> String
> polymorphicVar v = "Variable " ++ name v ++ " cannot have polymorphic type"

> typeSigTooGeneral :: TCEnv -> Doc -> TypeExpr -> TypeScheme -> String
> typeSigTooGeneral tcEnv what ty sigma = show $
>   vcat [text "Type signature too general", what,
>         text "Inferred type:" <+> ppTypeScheme tcEnv sigma,
>         text "Type signature:" <+> ppTypeExpr 0 ty]

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity c arity argc = show $
>   hsep [text "Constructor", ppQIdent c, text "requires",
>         int arity, text (plural arity "argument"),
>         text "in patterns, but is applied to", int argc]
>   where plural n x = if n == 1 then x else x ++ "s"

> nonFunctionType :: String -> Doc -> TCEnv -> Type -> String
> nonFunctionType what doc tcEnv ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType tcEnv ty,
>         text "Cannot be applied"]

> nonBinaryOp :: String -> Doc -> TCEnv -> Type -> String
> nonBinaryOp what doc tcEnv ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType tcEnv ty,
>         text "Cannot be used as binary operator"]

> typeMismatch :: String -> Doc -> TCEnv -> Type -> Type -> Doc -> String
> typeMismatch what doc tcEnv ty1 ty2 reason = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Inferred type:" <+> ppType tcEnv ty2,
>         text "Expected type:" <+> ppType tcEnv ty1,
>         reason]

> skolemEscapingScope :: TCEnv -> Doc -> Type -> String
> skolemEscapingScope tcEnv what ty = show $
>   vcat [text "Existential type escapes out of its scope", what,
>         text "Type:" <+> ppType tcEnv ty]

> invalidCType :: String -> TCEnv -> Type -> String
> invalidCType what tcEnv ty = show $
>   vcat [text ("Invalid " ++ what ++ " type in foreign declaration:"),
>         ppType tcEnv ty]

> recursiveType :: TCEnv -> Int -> Type -> Doc
> recursiveType tcEnv tv ty = incompatibleTypes tcEnv (TypeVariable tv) ty

> incompatibleTypes :: TCEnv -> Type -> Type -> Doc
> incompatibleTypes tcEnv ty1 ty2 =
>   sep [text "Types" <+> ppType tcEnv ty1,
>        nest 2 (text "and" <+> ppType tcEnv ty2),
>        text "are incompatible"]

\end{verbatim}
