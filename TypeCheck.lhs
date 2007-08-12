% -*- LaTeX -*-
% $Id: TypeCheck.lhs 2439 2007-08-12 22:16:58Z wlux $
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

The result of type checking is a (flat) top-level environment
containing the types of all constructors, variables, and functions
defined in a program. In addition, a type annotated source module or
goal is returned.
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
> infixl 1 >>-, >>=-

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

> (>>-) :: Monad m => m (a,b) -> (a -> m ()) -> m b
> m >>- f =
>   do
>     (x,y) <- m
>     f x
>     return y

> (>>=-) :: Monad m => m (a,c) -> (a -> m b) -> m (b,c)
> m >>=- f =
>   do
>     (x,z) <- m
>     y <- f x
>     return (y,z)

\end{verbatim}
Before checking the function declarations of a module, the compiler
adds the types of all data and newtype constructors defined in the
current module to the type environment.
\begin{verbatim}

> typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> [TopDecl a]
>           -> Error (ValueEnv,[TopDecl Type])
> typeCheck m tcEnv tyEnv ds =
>   run (do
>          vds' <- tcDecls m tcEnv [d | BlockDecl d <- vds]
>          tyEnv' <- fetchSt
>          theta <- liftSt fetchSt
>          return (subst theta tyEnv',
>                  map untyped tds ++
>                  map (BlockDecl . fmap (subst theta)) vds'))
>       (foldr (bindConstrs m tcEnv) tyEnv tds)
>   where (tds,vds) = partition isTypeDecl ds

\end{verbatim}
Type checking of a goal is simpler because there are no type
declarations.
\begin{verbatim}

> typeCheckGoal :: ModuleIdent -> TCEnv -> ValueEnv -> Goal a
>               -> Error (ValueEnv,Goal Type)
> typeCheckGoal m tcEnv tyEnv g =
>   run (do
>          g' <- tcGoal m tcEnv g
>          tyEnv' <- fetchSt
>          theta <- liftSt fetchSt
>          return (subst theta tyEnv',fmap (subst theta) g'))
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

> bindConstrs :: ModuleIdent -> TCEnv -> TopDecl a -> ValueEnv -> ValueEnv
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

> bindTypeSigs :: Decl a -> SigEnv -> SigEnv
> bindTypeSigs (TypeSig _ vs ty) env = foldr (flip bindEnv ty) env vs 
> bindTypeSigs _ env = env
        
\end{verbatim}
\paragraph{Declaration Groups}
Before type checking a group of declarations, a dependency analysis is
performed and the declaration group is split into minimal nested
binding groups which are checked separately. Within each binding
group, first the type environment is extended with new bindings for
all variables and functions defined in the group. Next, types are
inferred for all declarations without an explicit type signature and
the inferred types are then generalized. Finally, the types of all
explicitly typed declarations are checked.

The idea of checking the explicitly typed declarations after the
implicitly typed declarations is due to Mark P.\ Jones' ``Typing
Haskell in Haskell'' paper~\cite{Jones99:THiH}. It has the advantage
of inferring more general types. For instance, given the declarations
\begin{verbatim}
  f :: a -> Bool
  f x = (x==x) || g True
  g y = (y<=y) || f True
\end{verbatim}
the compiler will infer type \texttt{a -> Bool} for \texttt{g} if
\texttt{f} is checked after inferring a type for \texttt{g}, but only
type \texttt{Bool -> Bool} if both declarations are checked together.

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

> tcDecls :: ModuleIdent -> TCEnv -> [Decl a] -> TcState [Decl Type]
> tcDecls m tcEnv ds =
>   do
>     dss' <-
>       mapM (tcDeclGroup m tcEnv (foldr bindTypeSigs noSigs ods))
>            (scc bv (qfv m) vds)
>     return (map untyped ods ++ concat dss')
>   where (vds,ods) = partition isValueDecl ds

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> [Decl a]
>             -> TcState [Decl Type]
> tcDeclGroup m tcEnv _ [ForeignDecl p cc s ie f ty] =
>   do
>     tcForeignFunct m tcEnv p cc ie f ty
>     return [ForeignDecl p cc s ie f ty]
> tcDeclGroup m tcEnv sigs [FreeDecl p vs] =
>   do
>     bindDeclVars m tcEnv sigs p vs
>     return [FreeDecl p vs]
> tcDeclGroup m tcEnv sigs ds =
>   do
>     tyEnv0 <- fetchSt
>     mapM_ (bindDecl m tcEnv sigs) ds
>     impDs' <- mapM (tcDecl m tcEnv) impDs
>     tyEnv <- fetchSt
>     theta <- liftSt fetchSt
>     let tvs = [tv | (ty,PatternDecl _ t rhs) <- impDs',
>                     not (isVariablePattern t && isNonExpansive tyEnv rhs),
>                     tv <- typeVars (subst theta ty)]
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) tvs
>     mapM_ (uncurry (genDecl m . gen fvs . subst theta)) impDs'
>     expDs' <- mapM (uncurry (tcCheckDecl m tcEnv tyEnv)) expDs
>     return (map snd impDs' ++ expDs')
>   where (impDs,expDs) = partDecls sigs ds

> partDecls :: SigEnv -> [Decl a] -> ([Decl a],[(TypeExpr,Decl a)])
> partDecls sigs =
>   foldr (\d -> maybe (implicit d) (explicit d) (declTypeSig sigs d)) ([],[])
>   where implicit d ~(impDs,expDs) = (d:impDs,expDs)
>         explicit d ty ~(impDs,expDs) = (impDs,(ty,d):expDs)

> declTypeSig :: SigEnv -> Decl a -> Maybe TypeExpr
> declTypeSig sigs (FunctionDecl _ f _) = lookupEnv f sigs
> declTypeSig sigs (PatternDecl _ t _) =
>   case t of
>     VariablePattern _ v -> lookupEnv v sigs
>     _ -> Nothing

> bindDecl :: ModuleIdent -> TCEnv -> SigEnv -> Decl a -> TcState ()
> bindDecl m tcEnv sigs (FunctionDecl p f eqs) =
>   case lookupEnv f sigs of
>     Just ty -> updateSt_ (bindFun m f n (expandPolyType tcEnv ty))
>     Nothing ->
>       replicateM (n + 1) freshTypeVar >>=
>       updateSt_ . bindFun m f n . monoType . foldr1 TypeArrow
>   where n = eqnArity (head eqs)
> bindDecl m tcEnv sigs (PatternDecl p t _) =
>   case t of
>     VariablePattern _ v -> bindDeclVar True m tcEnv sigs p v
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

> tcDecl :: ModuleIdent -> TCEnv -> Decl a -> TcState (Type,Decl Type)
> tcDecl m tcEnv (FunctionDecl p f eqs) =
>   do
>     tyEnv0 <- fetchSt
>     theta <- liftSt fetchSt
>     ty <- inst (varType f tyEnv0)
>     eqs' <- mapM (tcEquation m tcEnv (fsEnv (subst theta tyEnv0)) ty f) eqs
>     return (ty,FunctionDecl p f eqs')
> tcDecl m tcEnv d@(PatternDecl p t rhs) =
>   do
>     (ty,t') <- tcConstrTerm tcEnv p t
>     rhs' <-
>       tcRhs m tcEnv rhs >>-
>       unify p "pattern declaration" (ppDecl d) tcEnv ty
>     return (ty,PatternDecl p t' rhs')

> tcEquation :: ModuleIdent -> TCEnv -> Set Int -> Type -> Ident -> Equation a
>            -> TcState (Equation Type)
> tcEquation m tcEnv fs ty f eq@(Equation p lhs rhs) =
>   do
>     eq' <-
>       tcEqn m tcEnv p lhs rhs >>-
>       unify p "function declaration" (ppEquation eq) tcEnv ty
>     checkSkolems p tcEnv (text "Function:" <+> ppIdent f) fs ty
>     return eq'

> tcEqn :: ModuleIdent -> TCEnv -> Position -> Lhs a -> Rhs a
>       -> TcState (Type,Equation Type)
> tcEqn m tcEnv p lhs rhs =
>   do
>     bindLambdaVars m lhs
>     (tys,lhs') <- tcLhs tcEnv p lhs
>     (ty,rhs') <- tcRhs m tcEnv rhs
>     return (foldr TypeArrow ty tys,Equation p lhs' rhs')

> bindLambdaVars :: QuantExpr t => ModuleIdent -> t -> TcState ()
> bindLambdaVars m t = mapM_ (bindLambdaVar m) (bv t)

> bindLambdaVar :: ModuleIdent -> Ident -> TcState ()
> bindLambdaVar m v = freshTypeVar >>= updateSt_ . bindFun m v 0 . monoType

> tcGoal :: ModuleIdent -> TCEnv -> Goal a -> TcState (Goal Type)
> tcGoal m tcEnv (Goal p e ds) =
>   do
>     ds' <- tcDecls m tcEnv ds
>     (ty,e') <- tcExpr m tcEnv p e
>     checkSkolems p tcEnv (text "Goal:" <+> ppExpr 0 e) zeroSet ty
>     return (Goal p e' ds')

\end{verbatim}
The function \texttt{genDecl} saves the generalized type of a function
or variable declaration without a type signature in the type
environment. The type has been generalized already by
\texttt{tcDeclGroup}.
\begin{verbatim}

> genDecl :: ModuleIdent -> TypeScheme -> Decl a -> TcState ()
> genDecl m ty (FunctionDecl _ f eqs) =
>   updateSt_ (rebindFun m f (eqnArity (head eqs)) ty)
> genDecl m ty (PatternDecl _ t _) =
>   case t of
>     VariablePattern _ v -> updateSt_ (rebindFun m v 0 ty)
>     _ -> return ()

\end{verbatim}
The function \texttt{tcCheckDecl} checks the type of an explicitly
typed function or variable declaration. After inferring a type for the
declaration, the inferred type is compared with the type signature.
Since the inferred type of an explicitly typed function or variable
declaration is automatically an instance of its type signature (cf.\ 
\texttt{tcDecl} above), the type signature is correct only if the
inferred type matches the type signature exactly.
\begin{verbatim}

> tcCheckDecl :: ModuleIdent -> TCEnv -> ValueEnv -> TypeExpr -> Decl a
>             -> TcState (Decl Type)
> tcCheckDecl m tcEnv tyEnv sigTy d =
>   do
>     (ty,d') <- tcDecl m tcEnv d
>     theta <- liftSt fetchSt
>     let fvs = fvEnv (subst theta tyEnv)
>         ty' = subst theta ty
>     checkDeclSig tcEnv sigTy (if poly then gen fvs ty' else monoType ty') d'
>   where poly = isNonExpansive tyEnv d

> checkDeclSig :: TCEnv -> TypeExpr -> TypeScheme -> Decl a -> TcState (Decl a)
> checkDeclSig tcEnv sigTy sigma (FunctionDecl p f eqs)
>   | sigma == expandPolyType tcEnv sigTy = return (FunctionDecl p f eqs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Function:" <+> ppIdent f
> checkDeclSig tcEnv sigTy sigma (PatternDecl p t rhs)
>   | sigma == expandPolyType tcEnv sigTy = return (PatternDecl p t rhs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Variable:" <+> ppConstrTerm 0 t

> class Binding a where
>   isNonExpansive :: ValueEnv -> a -> Bool

> instance Binding a => Binding [a] where
>   isNonExpansive tyEnv = all (isNonExpansive tyEnv)

> instance Binding (Decl a) where
>   isNonExpansive _ (InfixDecl _ _ _ _) = True
>   isNonExpansive _ (TypeSig _ _ _) = True
>   isNonExpansive _ (FunctionDecl _ _ _) = True
>   isNonExpansive _ (ForeignDecl _ _ _ _ _ _) = True
>   isNonExpansive tyEnv (PatternDecl _ t rhs) =
>     isVariablePattern t && isNonExpansive tyEnv rhs
>   isNonExpansive _ (FreeDecl _ _) = False
>   isNonExpansive _ (TrustAnnot _ _ _) = True

> instance Binding (Rhs a) where
>   isNonExpansive tyEnv (SimpleRhs _ e ds) =
>     isNonExpansive tyEnv ds && isNonExpansive tyEnv e
>   isNonExpansive _ (GuardedRhs _ _) = False

> instance Binding (Expression a) where
>   isNonExpansive tyEnv = isNonExpansiveApp tyEnv 0

> isNonExpansiveApp :: ValueEnv -> Int -> Expression a -> Bool
> isNonExpansiveApp _ _ (Literal _ _) = True
> isNonExpansiveApp tyEnv n (Variable _ v)
>   | isRenamed (unqualify v) = n == 0 || n < arity v tyEnv
>   | otherwise = n < arity v tyEnv
> isNonExpansiveApp _ _ (Constructor _ _) = True
> isNonExpansiveApp tyEnv n (Paren e) = isNonExpansiveApp tyEnv n e
> isNonExpansiveApp tyEnv n (Typed e _) = isNonExpansiveApp tyEnv n e
> isNonExpansiveApp tyEnv _ (Tuple es) = isNonExpansive tyEnv es
> isNonExpansiveApp tyEnv _ (List _ es) = isNonExpansive tyEnv es
> isNonExpansiveApp tyEnv n (Apply f e) =
>   isNonExpansive tyEnv e && isNonExpansiveApp tyEnv (n + 1) f
> isNonExpansiveApp tyEnv n (InfixApply e1 op e2) =
>   isNonExpansiveApp tyEnv (n + 2) (infixOp op) &&
>   isNonExpansive tyEnv e1 && isNonExpansive tyEnv e2
> isNonExpansiveApp tyEnv n (LeftSection e op) =
>   isNonExpansiveApp tyEnv (n + 1) (infixOp op) && isNonExpansive tyEnv e
> isNonExpansiveApp _ n (Lambda _ ts _) = n < length ts
> isNonExpansiveApp tyEnv n (Let ds e) =
>   isNonExpansive tyEnv ds && isNonExpansiveApp tyEnv n e
> isNonExpansiveApp _ _ _ = False

\end{verbatim}
\paragraph{Foreign Functions}
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
regard to marshaling). The type of a dynamic function wrapper is
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
>         foreignArity (ForAll _ ty)
>           | isIO ty' = length tys + 1
>           | otherwise = length tys
>           where (tys,ty') = arrowUnapply ty
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
Note that the type attribute associated with a constructor or infix
pattern is the type of the whole pattern and not the type of the
constructor itself.
\begin{verbatim}

> tcLiteral :: Literal -> TcState Type
> tcLiteral (Char _) = return charType
> tcLiteral (Int _) = freshConstrained [intType,floatType]
> tcLiteral (Float _) = return floatType
> tcLiteral (String _) = return stringType

> tcLhs :: TCEnv -> Position -> Lhs a -> TcState ([Type],Lhs Type)
> tcLhs tcEnv p (FunLhs f ts) =
>   do
>     (tys,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv p) ts
>     return (tys,FunLhs f ts')
> tcLhs tcEnv p (OpLhs t1 op t2) =
>   do
>     (ty1,t1') <- tcConstrTerm tcEnv p t1
>     (ty2,t2') <- tcConstrTerm tcEnv p t2
>     return ([ty1,ty2],OpLhs t1' op t2')
> tcLhs tcEnv p (ApLhs lhs ts) =
>   do
>     (tys1,lhs') <- tcLhs tcEnv p lhs
>     (tys2,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv p) ts
>     return (tys1 ++ tys2,ApLhs lhs' ts')

> tcConstrTerm :: TCEnv -> Position -> ConstrTerm a
>              -> TcState (Type,ConstrTerm Type)
> tcConstrTerm _ _ (LiteralPattern _ l) =
>   do
>     ty <- tcLiteral l
>     return (ty,LiteralPattern ty l)
> tcConstrTerm _ _ (NegativePattern _ op l) =
>   do
>     ty <- tcLiteral l
>     return (ty,NegativePattern ty op l)
> tcConstrTerm _ _ (VariablePattern _ v) =
>   do
>     ty <- fetchSt >>= inst . varType v
>     return (ty,VariablePattern ty v)
> tcConstrTerm tcEnv p t@(ConstructorPattern _ c ts) =
>   do
>     (ty,ts') <- tcConstrApp tcEnv p (ppConstrTerm 0 t) c ts
>     return (ty,ConstructorPattern ty c ts')
> tcConstrTerm tcEnv p t@(InfixPattern _ t1 op t2) =
>   do
>     (ty,[t1',t2']) <- tcConstrApp tcEnv p (ppConstrTerm 0 t) op [t1,t2]
>     return (ty,InfixPattern ty t1' op t2')
> tcConstrTerm tcEnv p (ParenPattern t) =
>   do
>     (ty,t') <- tcConstrTerm tcEnv p t
>     return (ty,ParenPattern t')
> tcConstrTerm tcEnv p (TuplePattern ts) =
>   do
>     (tys,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv p) ts
>     return (tupleType tys,TuplePattern ts')
> tcConstrTerm tcEnv p t@(ListPattern _ ts) =
>   do
>     ty <- freshTypeVar
>     ts' <- mapM (tcElem (ppConstrTerm 0 t) ty) ts
>     return (listType ty,ListPattern (listType ty) ts')
>   where tcElem doc ty t =
>           tcConstrTerm tcEnv p t >>-
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 tcEnv ty
> tcConstrTerm tcEnv p t@(AsPattern v t') =
>   do
>     ty <- fetchSt >>= inst . varType v
>     t'' <-
>       tcConstrTerm tcEnv p t' >>-
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv ty
>     return (ty,AsPattern v t'')
> tcConstrTerm tcEnv p (LazyPattern t) =
>   do
>     (ty,t') <- tcConstrTerm tcEnv p t
>     return (ty,LazyPattern t')

> tcConstrApp :: TCEnv -> Position -> Doc -> QualIdent -> [ConstrTerm a]
>             -> TcState (Type,[ConstrTerm Type])
> tcConstrApp tcEnv p doc c ts =
>   do
>     tyEnv <- fetchSt
>     (tys,ty) <- liftM arrowUnapply (skol (conType c tyEnv))
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     ts' <- zipWithM (tcConstrArg tcEnv p doc) ts tys
>     return (ty,ts')
>   where n = length ts

> tcConstrArg :: TCEnv -> Position -> Doc -> ConstrTerm a -> Type
>             -> TcState (ConstrTerm Type)
> tcConstrArg tcEnv p doc t ty =
>   tcConstrTerm tcEnv p t >>-
>   unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv ty

> tcRhs :: ModuleIdent -> TCEnv -> Rhs a -> TcState (Type,Rhs Type)
> tcRhs m tcEnv (SimpleRhs p e ds) =
>   do
>     ds' <- tcDecls m tcEnv ds
>     (ty,e') <- tcExpr m tcEnv p e
>     return (ty,SimpleRhs p e' ds')
> tcRhs m tcEnv (GuardedRhs es ds) =
>   do
>     ds' <- tcDecls m tcEnv ds
>     gty <- guardType es
>     ty <- freshTypeVar
>     es' <- mapM (tcCondExpr m tcEnv gty ty) es
>     return (ty,GuardedRhs es' ds')
>   where guardType es
>           | length es > 1 = return boolType
>           | otherwise = freshConstrained [successType,boolType]

> tcCondExpr :: ModuleIdent -> TCEnv -> Type -> Type -> CondExpr a
>            -> TcState (CondExpr Type)
> tcCondExpr m tcEnv gty ty (CondExpr p g e) =
>   do
>     g' <- tcExpr m tcEnv p g >>- unify p "guard" (ppExpr 0 g) tcEnv gty
>     e' <-
>       tcExpr m tcEnv p e >>-
>       unify p "guarded expression" (ppExpr 0 e) tcEnv ty
>     return (CondExpr p g' e')

> tcExpr :: ModuleIdent -> TCEnv -> Position -> Expression a
>        -> TcState (Type,Expression Type)
> tcExpr _ _ _ (Literal _ l) =
>   do
>     ty <- tcLiteral l
>     return (ty,Literal ty l)
> tcExpr m tcEnv p (Variable _ v) =
>   do
>     ty <- fetchSt >>= inst . funType v
>     return (ty,Variable ty v)
> tcExpr m tcEnv p (Constructor _ c) =
>   do
>     ty <- fetchSt >>= inst . conType c
>     return (ty,Constructor ty c)
> tcExpr m tcEnv p (Typed e sig) =
>   do
>     tyEnv0 <- fetchSt
>     ty <- inst sigma'
>     e' <-
>       tcExpr m tcEnv p e >>-
>       unify p "explicitly typed expression" (ppExpr 0 e) tcEnv ty
>     theta <- liftSt fetchSt
>     let sigma = gen (fvEnv (subst theta tyEnv0)) (subst theta ty)
>     unless (sigma == sigma')
>       (errorAt p (typeSigTooGeneral tcEnv (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return (ty,Typed e' sig)
>   where sigma' = expandPolyType tcEnv sig
> tcExpr m tcEnv p (Paren e) =
>   do
>     (ty,e') <- tcExpr m tcEnv p e
>     return (ty,Paren e')
> tcExpr m tcEnv p (Tuple es) =
>   do
>     (tys,es') <- liftM unzip $ mapM (tcExpr m tcEnv p) es
>     return (tupleType tys,Tuple es')
> tcExpr m tcEnv p e@(List _ es) =
>   do
>     ty <- freshTypeVar
>     es' <- mapM (tcElem (ppExpr 0 e) ty) es
>     return (listType ty,List (listType ty) es')
>   where tcElem doc ty e =
>           tcExpr m tcEnv p e >>-
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e) tcEnv ty
> tcExpr m tcEnv p (ListCompr e qs) =
>   do
>     qs' <- mapM (tcQual m tcEnv p) qs
>     (ty,e') <- tcExpr m tcEnv p e
>     return (listType ty,ListCompr e' qs')
> tcExpr m tcEnv p e@(EnumFrom e1) =
>   do
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     return (listType intType,EnumFrom e1')
> tcExpr m tcEnv p e@(EnumFromThen e1 e2) =
>   do
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     e2' <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     return (listType intType,EnumFromThen e1' e2')
> tcExpr m tcEnv p e@(EnumFromTo e1 e2) =
>   do
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     e2' <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     return (listType intType,EnumFromTo e1' e2')
> tcExpr m tcEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     e2' <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     e3' <-
>       tcExpr m tcEnv p e3 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) tcEnv intType
>     return (listType intType,EnumFromThenTo e1' e2' e3')
> tcExpr m tcEnv p e@(UnaryMinus op e1) =
>   do
>     ty <- opType op
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv ty
>     return (ty,UnaryMinus op e1')
>   where opType op
>           | op == minusId = freshConstrained [intType,floatType]
>           | op == fminusId = return floatType
>           | otherwise = internalError ("tcExpr unary " ++ name op)
> tcExpr m tcEnv p e@(Apply e1 e2) =
>   do
>     ((alpha,beta),e1') <-
>       tcExpr m tcEnv p e1 >>=-
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>               tcEnv
>     e2' <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             tcEnv alpha
>     return (beta,Apply e1' e2')
> tcExpr m tcEnv p e@(InfixApply e1 op e2) =
>   do
>     ((alpha,beta,gamma),op') <-
>       tcInfixOp m tcEnv p op >>=-
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv alpha
>     e2' <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv beta
>     return (gamma,InfixApply e1' op' e2')
> tcExpr m tcEnv p e@(LeftSection e1 op) =
>   do
>     ((alpha,beta),op') <-
>       tcInfixOp m tcEnv p op >>=-
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               tcEnv
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv alpha
>     return (beta,LeftSection e1' op')
> tcExpr m tcEnv p e@(RightSection op e1) =
>   do
>     ((alpha,beta,gamma),op') <-
>       tcInfixOp m tcEnv p op >>=-
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv beta
>     return (TypeArrow alpha gamma,RightSection op' e1')
> tcExpr m tcEnv _ (Lambda p ts e) =
>   do
>     bindLambdaVars m ts
>     (tys,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv p) ts
>     (ty,e') <- tcExpr m tcEnv p e
>     return (foldr TypeArrow ty tys,Lambda p ts' e')
> tcExpr m tcEnv p (Let ds e) =
>   do
>     ds' <- tcDecls m tcEnv ds
>     (ty,e') <- tcExpr m tcEnv p e
>     return (ty,Let ds' e')
> tcExpr m tcEnv p (Do sts e) =
>   do
>     sts' <- mapM (tcStmt m tcEnv p) sts
>     ty <- liftM ioType freshTypeVar
>     e' <- tcExpr m tcEnv p e >>- unify p "statement" (ppExpr 0 e) tcEnv ty
>     return (ty,Do sts' e')
> tcExpr m tcEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     e1' <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv boolType
>     (ty,e2') <- tcExpr m tcEnv p e2
>     e3' <-
>       tcExpr m tcEnv p e3 >>-
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>             tcEnv ty
>     return (ty,IfThenElse e1' e2' e3')
> tcExpr m tcEnv p (Case e as) =
>   do
>     (tyLhs,e') <- tcExpr m tcEnv p e
>     tyRhs <- freshTypeVar
>     as' <- mapM (tcAlt m tcEnv tyLhs tyRhs) as
>     return (tyRhs,Case e' as')

> tcAlt :: ModuleIdent -> TCEnv -> Type -> Type -> Alt a -> TcState (Alt Type)
> tcAlt m tcEnv tyLhs tyRhs a@(Alt p t rhs) =
>   do
>     bindLambdaVars m t
>     t' <-
>       tcConstrTerm tcEnv p t >>-
>       unify p "case pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>             tcEnv tyLhs
>     rhs' <- tcRhs m tcEnv rhs >>- unify p "case branch" doc tcEnv tyRhs
>     return (Alt p t' rhs')
>   where doc = ppAlt a

> tcQual :: ModuleIdent -> TCEnv -> Position -> Statement a
>        -> TcState (Statement Type)
> tcQual m tcEnv p (StmtExpr e) =
>   do
>     e' <- tcExpr m tcEnv p e >>- unify p "guard" (ppExpr 0 e) tcEnv boolType
>     return (StmtExpr e')
> tcQual m tcEnv _ q@(StmtBind p t e) =
>   do
>     bindLambdaVars m t
>     (ty,t') <- tcConstrTerm tcEnv p t
>     e' <-
>       tcExpr m tcEnv p e >>-
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (listType ty)
>     return (StmtBind p t' e')
> tcQual m tcEnv _ (StmtDecl ds) =
>   do
>     ds' <- tcDecls m tcEnv ds
>     return (StmtDecl ds')

> tcStmt :: ModuleIdent -> TCEnv -> Position -> Statement a
>        -> TcState (Statement Type)
> tcStmt m tcEnv p (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     e' <-
>       tcExpr m tcEnv p e >>-
>       unify p "statement" (ppExpr 0 e) tcEnv (ioType alpha)
>     return (StmtExpr e')
> tcStmt m tcEnv _ st@(StmtBind p t e) =
>   do
>     bindLambdaVars m t
>     (ty,t') <- tcConstrTerm tcEnv p t
>     e' <-
>       tcExpr m tcEnv p e >>-
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (ioType ty)
>     return (StmtBind p t' e')
> tcStmt m tcEnv _ (StmtDecl ds) =
>   do
>     ds' <- tcDecls m tcEnv ds
>     return (StmtDecl ds')

> tcInfixOp :: ModuleIdent -> TCEnv -> Position -> InfixOp a
>           -> TcState (Type,InfixOp Type)
> tcInfixOp m tcEnv p (InfixOp a op) =
>   do
>     (ty,_) <- tcExpr m tcEnv p (Variable a op)
>     return (ty,InfixOp ty op)
> tcInfixOp m tcEnv p (InfixConstr a op) =
>   do
>     (ty,_) <- tcExpr m tcEnv p (Constructor a op)
>     return (ty,InfixConstr ty op)

\end{verbatim}
The function \texttt{tcArrow} checks that its argument can be used as
an arrow type $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$. Similarly, the function \texttt{tcBinary} checks
that its argument can be used as an arrow type
$\alpha\rightarrow\beta\rightarrow\gamma$ and returns the triple
$(\alpha,\beta,\gamma)$.
\begin{verbatim}

> tcArrow :: Position -> String -> Doc -> TCEnv -> Type -> TcState (Type,Type)
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

> unify :: Position -> String -> Doc -> TCEnv -> Type -> Type -> TcState ()
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

> isVariablePattern :: ConstrTerm a -> Bool
> isVariablePattern (VariablePattern _ _) = True
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
The function \texttt{untyped} is used when transforming annotated
syntax tree nodes into typed syntax tree nodes without adding type
information. This is useful for nodes which contain no attributes
themselves, e.g., operator fixity declarations.
\begin{verbatim}

> untyped :: Functor f => f a -> f Type
> untyped = fmap (internalError "untyped")

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
