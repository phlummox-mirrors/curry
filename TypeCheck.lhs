% -*- LaTeX -*-
% $Id: TypeCheck.lhs 1765 2005-09-12 13:42:51Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeCheck.lhs}
\section{Type Checking Curry Programs}
This module implements the type checker of the Curry compiler. The
type checker is invoked after the syntactic correctness of the program
has been verified. Local variables have been renamed already. Thus the
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
> import Set
> import Combined
> import SCC
> import TypeSubst
> import Utils
> import List
> import Monad
> import Maybe

> infixl 5 $-$

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

\end{verbatim}
Type checking proceeds as follows. First, the type constructor
environment is initialized by adding all types defined in the current
module. Next, the types of all data constructors are entered into the
type environment and then a type inference for all function and value
definitions is performed. The type checker returns the resulting type
constructor and type environments.
\begin{verbatim}

> typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> [TopDecl] -> (TCEnv,ValueEnv)
> typeCheck m tcEnv tyEnv ds =
>   run (tcDecls m tcEnv' [d | BlockDecl d <- vds] >>
>        liftSt fetchSt >>= \theta -> fetchSt >>= \tyEnv' ->
>        return (tcEnv',subst theta tyEnv'))
>       (foldr (bindConstrs m tcEnv') tyEnv tds)
>   where (tds,vds) = partition isTypeDecl ds
>         tcEnv' = bindTypes m tds tcEnv

\end{verbatim}
Type checking of a goal expression is simpler because the type
constructor environment is fixed already and there are no
type declarations in a goal.
\begin{verbatim}

> typeCheckGoal :: TCEnv -> ValueEnv -> Goal -> ValueEnv
> typeCheckGoal tcEnv tyEnv (Goal p e ds) =
>    run (tcRhs emptyMIdent tcEnv (SimpleRhs p e ds) >>
>         liftSt fetchSt >>= \theta -> fetchSt >>= \tyEnv' ->
>         return (subst theta tyEnv')) tyEnv

\end{verbatim}
The type checker makes use of nested state monads in order to
maintain the type environment, the current substitution, and a counter
which is used for generating fresh type variables.
\begin{verbatim}

> type TcState a = StateT ValueEnv (StateT TypeSubst (StateT Int Id)) a

> run :: TcState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt (callSt m tyEnv) idSubst) 1

\end{verbatim}
\paragraph{Defining Types}
Before type checking starts, the types defined in the local module
have to be entered into the type constructor environment. All type
synonyms occurring in the definitions are fully expanded and all type
constructors are qualified with the name of the module in which they
are defined. This is possible because Curry does not allow (mutually)
recursive type synonyms.

Note that \texttt{bindTC} is passed the \emph{final} type constructor
environment in order to handle the expansion of type synonyms. This
does not lead to termination problems because \texttt{sortTypeDecls}
checks that there are no recursive type synonyms.
\begin{verbatim}

> bindTypes :: ModuleIdent -> [TopDecl] -> TCEnv -> TCEnv
> bindTypes m ds tcEnv = tcEnv'
>   where tcEnv' = foldr (bindTC m tcEnv') tcEnv (sortTypeDecls m ds)

> bindTC :: ModuleIdent -> TCEnv -> TopDecl -> TCEnv -> TCEnv
> bindTC m tcEnv (DataDecl _ tc tvs cs) =
>   bindTypeInfo DataType m tc tvs (map (Just . constr) cs)
> bindTC m tcEnv (NewtypeDecl _ tc tvs (NewConstrDecl _ _ c _)) =
>   bindTypeInfo RenamingType m tc tvs c
> bindTC m tcEnv (TypeDecl _ tc tvs ty) =
>   bindTypeInfo AliasType m tc tvs (expandMonoType tcEnv tvs ty)
> bindTC _ _ (BlockDecl _) = id

> sortTypeDecls :: ModuleIdent -> [TopDecl] -> [TopDecl]
> sortTypeDecls m = map (typeDecl m) . scc bound free
>   where bound (DataDecl _ tc _ _) = [tc]
>         bound (NewtypeDecl _ tc _ _) = [tc]
>         bound (TypeDecl _ tc _ _) = [tc]
>         bound (BlockDecl _) = []
>         free (DataDecl _ _ _ _) = []
>         free (NewtypeDecl _ _ _ _) = []
>         free (TypeDecl _ _ _ ty) = ft m ty []
>         free (BlockDecl _) = []

> typeDecl :: ModuleIdent -> [TopDecl] -> TopDecl
> typeDecl _ [] = internalError "typeDecl"
> typeDecl _ [d@(DataDecl _ _ _ _)] = d
> typeDecl _ [d@(NewtypeDecl _ _ _ _)] = d
> typeDecl m [d@(TypeDecl p tc _ ty)]
>   | tc `elem` ft m ty [] = errorAt p (recursiveTypes [tc])
>   | otherwise = d
> typeDecl _ (TypeDecl p tc _ _ : ds) =
>   errorAt p (recursiveTypes (tc : [tc' | TypeDecl _ tc' _ _ <- ds]))

> ft :: ModuleIdent -> TypeExpr -> [Ident] -> [Ident]
> ft m (ConstructorType tc tys) tcs =
>   maybe id (:) (localIdent m tc) (foldr (ft m) tcs tys)
> ft _ (VariableType _) tcs = tcs
> ft m (TupleType tys) tcs = foldr (ft m) tcs tys
> ft m (ListType ty) tcs = ft m ty tcs
> ft m (ArrowType ty1 ty2) tcs = ft m ty1 $ ft m ty2 $ tcs

\end{verbatim}
\paragraph{Defining Data Constructors}
In the next step, the types of all data and newtype constructors are
entered into the type environment. All type synonyms occurring in
their types are expanded as well.

We have to be careful with existentially quantified type variables for
data and newtype constructors. An existentially quantified type
variable may shadow a universally quantified variable from the left
hand side of the type declaration. In order to avoid wrong indices
being assigned to these variables, we replace all shadowed variables
in the left hand side by \texttt{anonId} before passing them to
\texttt{expandMonoTypes}.
\begin{verbatim}

> bindConstrs :: ModuleIdent -> TCEnv -> TopDecl -> ValueEnv -> ValueEnv
> bindConstrs m tcEnv (DataDecl _ tc tvs cs) tyEnv = foldr bind tyEnv cs
>   where ty0 = constrType m tc tvs
>         bind (ConstrDecl _ evs c tys) =
>           bindConstr DataConstructor m tcEnv tvs evs c tys ty0
>         bind (ConOpDecl _ evs ty1 op ty2) =
>           bindConstr DataConstructor m tcEnv tvs evs op [ty1,ty2] ty0
> bindConstrs m tcEnv (NewtypeDecl _ tc tvs nc) tyEnv = bind nc tyEnv
>   where ty0 = constrType m tc tvs
>         bind (NewConstrDecl _ evs c ty) =
>           bindConstr NewtypeConstructor m tcEnv tvs evs c [ty] ty0
> bindConstrs _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindConstrs _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: (QualIdent -> ExistTypeScheme -> ValueInfo) -> ModuleIdent
>            -> TCEnv -> [Ident] -> [Ident] -> Ident -> [TypeExpr] -> Type
>            -> ValueEnv -> ValueEnv
> bindConstr f m tcEnv tvs evs c tys ty0 =
>   bindGlobalInfo f m c
>     (ForAllExist (length tvs) (length evs) (foldr TypeArrow ty0 tys'))
>   where tys' = expandMonoTypes tcEnv (cleanTVars tvs evs) tys

> constrType :: ModuleIdent -> Ident -> [Ident] -> Type
> constrType m tc tvs =
>   TypeConstructor (qualifyWith m tc) (map TypeVariable [0..length tvs-1])

> cleanTVars :: [Ident] -> [Ident] -> [Ident]
> cleanTVars tvs evs = [if tv `elem` evs then anonId else tv | tv <- tvs]

\end{verbatim}
\paragraph{Type Signatures}
The type checker collects type signatures in a flat environment. All
anonymous variables occurring in a signature are replaced by fresh
names. However, the type is not expanded so that the signature is
available for use in the error message that is printed when the
inferred type is less general than the signature.
\begin{verbatim}

> type SigEnv = Env Ident TypeExpr

> noSigs :: SigEnv
> noSigs = emptyEnv

> bindTypeSig :: Ident -> TypeExpr -> SigEnv -> SigEnv
> bindTypeSig = bindEnv

> bindTypeSigs :: Decl -> SigEnv -> SigEnv
> bindTypeSigs (TypeSig _ vs ty) env =
>   foldr (flip bindTypeSig (nameSigType ty)) env vs 
> bindTypeSigs _ env = env

> lookupTypeSig :: Ident -> SigEnv -> Maybe TypeExpr
> lookupTypeSig = lookupEnv

> nameSigType :: TypeExpr -> TypeExpr
> nameSigType ty = fst (nameType ty (filter (`notElem` fv ty) nameSupply))

> nameTypes :: [TypeExpr] -> [Ident] -> ([TypeExpr],[Ident])
> nameTypes (ty:tys) tvs = (ty':tys',tvs'')
>   where (ty',tvs') = nameType ty tvs
>         (tys',tvs'') = nameTypes tys tvs'
> nameTypes [] tvs = ([],tvs)

> nameType :: TypeExpr -> [Ident] -> (TypeExpr,[Ident])
> nameType (ConstructorType tc tys) tvs = (ConstructorType tc tys',tvs')
>   where (tys',tvs') = nameTypes tys tvs
> nameType (VariableType tv) (tv':tvs)
>   | tv == anonId = (VariableType tv',tvs)
>   | otherwise = (VariableType tv,tv':tvs)
> nameType (TupleType tys) tvs = (TupleType tys',tvs')
>   where (tys',tvs') = nameTypes tys tvs
> nameType (ListType ty) tvs = (ListType ty',tvs')
>   where (ty',tvs') = nameType ty tvs
> nameType (ArrowType ty1 ty2) tvs = (ArrowType ty1' ty2',tvs'')
>   where (ty1',tvs') = nameType ty1 tvs
>         (ty2',tvs'') = nameType ty2 tvs'
        
\end{verbatim}
\paragraph{Type Inference}
Before type checking a group of declarations, a dependency analysis is
performed and the declaration group is eventually transformed into
nested declaration groups which are checked separately. Within each
declaration group, first the left hand sides of all declarations are
typed introducing new bindings for their bound variables. Next, the
right hand sides of the declarations are typed in the extended type
environment and the inferred types are unified with the left hand side
types. Finally, the types of all defined functions are generalized.
The generalization step will also check that the type signatures given
by the user match the inferred types.
\begin{verbatim}

> tcDecls :: ModuleIdent -> TCEnv -> [Decl] -> TcState ()
> tcDecls m tcEnv ds =
>   mapM_ (tcDeclGroup m tcEnv (foldr bindTypeSigs noSigs ods))
>         (scc bv (qfv m) vds)
>   where (vds,ods) = partition isValueDecl ds

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> [Decl] -> TcState ()
> tcDeclGroup m tcEnv _ [ForeignDecl p cc ie f ty] =
>   tcForeignFunct m tcEnv p cc ie f ty
> tcDeclGroup m tcEnv sigs [FreeDecl p vs] =
>   mapM_ (tcVariable m tcEnv sigs False p) vs
> tcDeclGroup m tcEnv sigs ds =
>   do
>     tyEnv0 <- fetchSt
>     tys <- mapM (tcDeclLhs m tcEnv sigs) ds
>     zipWithM_ (tcDeclRhs m tcEnv) tys ds
>     theta <- liftSt fetchSt
>     let lvs = fvEnv (subst theta tyEnv0)
>     zipWithM_ (genDecl m tcEnv sigs . gen lvs . subst theta) tys ds

> tcDeclLhs :: ModuleIdent -> TCEnv -> SigEnv -> Decl -> TcState Type
> tcDeclLhs m tcEnv sigs (FunctionDecl p f _) = tcVariable m tcEnv sigs True p f
> tcDeclLhs m tcEnv sigs (PatternDecl p t _) = tcConstrTerm m tcEnv sigs p t

> tcDeclRhs :: ModuleIdent -> TCEnv -> Type -> Decl -> TcState ()
> tcDeclRhs m tcEnv ty (FunctionDecl _ f eqs) = mapM_ (tcEqn m tcEnv ty) eqs
>   where tcEqn m tcEnv ty eq@(Equation p _ _) =
>           tcEquation m tcEnv eq >>=
>           unify p "function declaration" (ppEquation eq) m ty
> tcDeclRhs m tcEnv ty (PatternDecl p t rhs) =
>   tcRhs m tcEnv rhs >>= unify p "pattern binding" (ppConstrTerm 0 t) m ty

\end{verbatim}
Argument and result types of foreign functions using the
\texttt{ccall} calling convention are restricted to the basic types
\texttt{Bool}, \texttt{Char}, \texttt{Int}, \texttt{Float},
\texttt{Ptr} and \texttt{FunPtr}. In addition, $\texttt{IO}\;t$ is a
legitimate result type when $t$ is either one of the basic types or
\texttt{()}. Furthermore, the type of a dynamic function wrapper must
be of the form $(\texttt{FunPtr}\;t) \rightarrow t$, where $t$ is a
valid foreign function type, and the type of a foreign address must be
either $\texttt{Ptr}\;a$ or $\texttt{FunPtr}\;a$, where $a$ is an
arbitrary type.
\begin{verbatim}

> tcForeignFunct :: ModuleIdent -> TCEnv -> Position -> CallConv
>                -> Maybe String -> Ident -> TypeExpr -> TcState ()
> tcForeignFunct m tcEnv p cc ie f ty =
>   updateSt_ (bindFun m f (checkForeignType cc (expandPolyType tcEnv ty)))
>   where checkForeignType CallConvPrimitive ty = ty
>         checkForeignType CallConvCCall (ForAll n ty)
>           | ie == Just "dynamic" = ForAll n (checkCDynCallType m p ty)
>           | maybe False ('&' `elem`) ie = ForAll n (checkCAddrType m p ty)
>           | otherwise = ForAll n (checkCCallType m p ty)

> checkCCallType :: ModuleIdent -> Position -> Type -> Type
> checkCCallType m p (TypeArrow ty1 ty2)
>   | isCArgType ty1 = TypeArrow ty1 (checkCCallType m p ty2)
>   | otherwise = errorAt p (invalidCType "argument" m ty1)
> checkCCallType m p ty
>   | isCRetType ty = ty
>   | otherwise = errorAt p (invalidCType "result" m ty)

> checkCDynCallType :: ModuleIdent -> Position -> Type -> Type
> checkCDynCallType m p (TypeArrow (TypeConstructor tc [ty1]) ty2)
>   | tc == qFunPtrId && ty1 == ty2 =
>       TypeArrow (TypeConstructor tc [checkCCallType m p ty1]) ty2
> checkCDynCallType m p ty = errorAt p (invalidCType "dynamic function" m ty)

> checkCAddrType :: ModuleIdent -> Position -> Type -> Type
> checkCAddrType m p ty
>   | isCPtrType ty = ty
>   | otherwise = errorAt p (invalidCType "static address" m ty)

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
In Curry we cannot generalize the types of let-bound variables because
they can refer to logic variables. Without this monomorphism
restriction unsound code like
\begin{verbatim}
bug = x =:= 1 & x =:= 'a'
  where x :: a
        x = fresh
fresh :: a
fresh = x where x free
\end{verbatim}
could be written. Note that \texttt{fresh} has the polymorphic type
$\forall\alpha.\alpha$. This is correct because \texttt{fresh} is a
function and therefore returns a different variable at each
invocation.

The code in \texttt{genDecl} below also verifies that the inferred
type for a function matches its declared type. Since the type inferred
for the left hand side of a function or variable declaration is an
instance of its declared type -- provided a type signature is given --
it can only be more specific. Therefore, if the inferred type does not
match the type signature the declared type must be too general. No
check is necessary for the variables in variable and other pattern
declarations because the types of variables must be monomorphic, which
is checked in \texttt{tcVariable} below.
\begin{verbatim}

> genDecl :: ModuleIdent -> TCEnv -> SigEnv -> TypeScheme -> Decl -> TcState ()
> genDecl m tcEnv sigs sigma (FunctionDecl p f _) =
>   case lookupTypeSig f sigs of
>     Just sigTy
>       | sigma == expandPolyType tcEnv sigTy -> return ()
>       | otherwise -> errorAt p (typeSigTooGeneral m what sigTy sigma)
>     Nothing -> updateSt_ (rebindFun m f sigma)
>   where what = text "Function:" <+> ppIdent f
> genDecl _ _ _ _ (PatternDecl _ _ _) = return ()

> tcEquation :: ModuleIdent -> TCEnv -> Equation -> TcState Type
> tcEquation m tcEnv (Equation p lhs rhs) =
>   do
>     tyEnv0 <- fetchSt
>     tys <- mapM (tcConstrTerm m tcEnv noSigs p) ts
>     ty <- tcRhs m tcEnv rhs
>     checkSkolems p m (text "Function:" <+> ppIdent f) tyEnv0
>                  (foldr TypeArrow ty tys)
>   where (f,ts) = flatLhs lhs

> tcLiteral :: ModuleIdent -> Literal -> TcState Type
> tcLiteral _ (Char _) = return charType
> tcLiteral m (Int v _) =
>   do
>     ty <- freshConstrained [intType,floatType]
>     updateSt_ (bindFun m v (monoType ty))
>     return ty
> tcLiteral _ (Float _) = return floatType
> tcLiteral _ (String _) = return stringType

> tcVariable :: ModuleIdent -> TCEnv -> SigEnv -> Bool -> Position -> Ident
>            -> TcState Type
> tcVariable m tcEnv sigs poly p v =
>   case lookupTypeSig v sigs of
>     Just ty -> sigType m poly p v (expandPolyType tcEnv ty)
>     Nothing -> freshType m v
>   where sigType m poly p v ty
>           | poly || isMonoType ty = updateSt_ (bindFun m v ty) >> inst ty
>           | otherwise = errorAt p (polymorphicVar v)
>         freshType m v =
>           do
>             ty <- freshTypeVar
>             updateSt_ (bindFun m v (monoType ty))
>             return ty
>         isMonoType (ForAll n _) = n == 0

> tcConstrTerm :: ModuleIdent -> TCEnv -> SigEnv -> Position -> ConstrTerm
>              -> TcState Type
> tcConstrTerm m tcEnv sigs p (LiteralPattern l) = tcLiteral m l
> tcConstrTerm m tcEnv sigs p (NegativePattern _ l) = tcLiteral m l
> tcConstrTerm m tcEnv sigs p (VariablePattern v) =
>   tcVariable m tcEnv sigs False p v
> tcConstrTerm m tcEnv sigs p t@(ConstructorPattern c ts) =
>   do
>     tyEnv <- fetchSt
>     ty <- skol (conType c tyEnv)
>     zipWithM_ (tcConstrArg m tcEnv sigs p (ppConstrTerm 0 t))
>               ts (arrowArgs ty)
>     return (arrowBase ty)
> tcConstrTerm m tcEnv sigs p t@(InfixPattern t1 op t2) =
>   do
>     tyEnv <- fetchSt
>     ty <- skol (conType op tyEnv)
>     zipWithM_ (tcConstrArg m tcEnv sigs p (ppConstrTerm 0 t))
>               [t1,t2] (arrowArgs ty)
>     return (arrowBase ty)
> tcConstrTerm m tcEnv sigs p (ParenPattern t) = tcConstrTerm m tcEnv sigs p t
> tcConstrTerm m tcEnv sigs p (TuplePattern ts)
>  | null ts = return unitType
>  | otherwise = liftM tupleType $ mapM (tcConstrTerm m tcEnv sigs p) ts   -- $
> tcConstrTerm m tcEnv sigs p t@(ListPattern ts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (tcElem (ppConstrTerm 0 t) ty) ts
>     return (listType ty)
>   where tcElem doc ty t =
>           tcConstrTerm m tcEnv sigs p t >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 m ty
> tcConstrTerm m tcEnv sigs p t@(AsPattern v t') =
>   do
>     ty <- tcConstrTerm m tcEnv sigs p (VariablePattern v)
>     tcConstrTerm m tcEnv sigs p t' >>=
>       unify p "pattern" (ppConstrTerm 0 t) m ty
>     return ty
> tcConstrTerm m tcEnv sigs p (LazyPattern t) = tcConstrTerm m tcEnv sigs p t

> tcConstrArg :: ModuleIdent -> TCEnv -> SigEnv -> Position -> Doc
>             -> ConstrTerm -> Type -> TcState ()
> tcConstrArg m tcEnv sigs p doc t ty =
>   tcConstrTerm m tcEnv sigs p t >>=
>   unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) m ty

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
>     tcExpr m tcEnv p g >>= unify p "guard" (ppExpr 0 g) m gty
>     tcExpr m tcEnv p e >>= unify p "guarded expression" (ppExpr 0 e) m ty

> tcExpr :: ModuleIdent -> TCEnv -> Position -> Expression -> TcState Type
> tcExpr m _ _ (Literal l) = tcLiteral m l
> tcExpr m tcEnv p (Variable v) = fetchSt >>= inst . funType v
> tcExpr m tcEnv p (Constructor c) = fetchSt >>= instExist . conType c
> tcExpr m tcEnv p (Typed e sig) =
>   do
>     tyEnv0 <- fetchSt
>     ty <- tcExpr m tcEnv p e
>     inst sigma' >>=
>       flip (unify p "explicitly typed expression" (ppExpr 0 e) m) ty
>     theta <- liftSt fetchSt
>     let sigma = gen (fvEnv (subst theta tyEnv0)) (subst theta ty)
>     unless (sigma == sigma')
>       (errorAt p (typeSigTooGeneral m (text "Expression:" <+> ppExpr 0 e)
>                  sig' sigma))
>     return ty
>   where sig' = nameSigType sig
>         sigma' = expandPolyType tcEnv sig'
> tcExpr m tcEnv p (Paren e) = tcExpr m tcEnv p e
> tcExpr m tcEnv p (Tuple es)
>   | null es = return unitType
>   | otherwise = liftM tupleType $ mapM (tcExpr m tcEnv p) es             -- $
> tcExpr m tcEnv p e@(List es) =
>   do
>     ty <- freshTypeVar
>     mapM_ (tcElem (ppExpr 0 e) ty) es
>     return (listType ty)
>   where tcElem doc ty e =
>           tcExpr m tcEnv p e >>=
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e) m ty
> tcExpr m tcEnv p (ListCompr e qs) =
>   do
>     mapM_ (tcQual m tcEnv p) qs
>     liftM listType (tcExpr m tcEnv p e)
> tcExpr m tcEnv p e@(EnumFrom e1) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     return (listType intType)
> tcExpr m tcEnv p e@(EnumFromThen e1 e2) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m intType
>     return (listType intType)
> tcExpr m tcEnv p e@(EnumFromTo e1 e2) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m intType
>     return (listType intType)
> tcExpr m tcEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m intType
>     tcExpr m tcEnv p e3 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) m intType
>     return (listType intType)
> tcExpr m tcEnv p e@(UnaryMinus op e1) =
>   do
>     ty <- opType op
>     tcExpr m tcEnv p e1 >>=
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m ty
>     return ty
>   where opType op
>           | op == minusId = freshConstrained [intType,floatType]
>           | op == fminusId = return floatType
>           | otherwise = internalError ("tcExpr unary " ++ name op)
> tcExpr m tcEnv p e@(Apply e1 e2) =
>   do
>     (alpha,beta) <-
>       tcExpr m tcEnv p e1 >>=
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m
>     tcExpr m tcEnv p e2 >>=
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             m alpha
>     return beta
> tcExpr m tcEnv p e@(InfixApply e1 op e2) =
>   do
>     (alpha,beta,gamma) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) m
>     tcExpr m tcEnv p e1 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m alpha
>     tcExpr m tcEnv p e2 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m beta
>     return gamma
> tcExpr m tcEnv p e@(LeftSection e1 op) =
>   do
>     (alpha,beta) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               m
>     tcExpr m tcEnv p e1 >>=
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m alpha
>     return beta
> tcExpr m tcEnv p e@(RightSection op e1) =
>   do
>     (alpha,beta,gamma) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) m
>     tcExpr m tcEnv p e1 >>=
>       unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m beta
>     return (TypeArrow alpha gamma)
> tcExpr m tcEnv p (Lambda ts e) =
>   do
>     tys <- mapM (tcConstrTerm m tcEnv noSigs p) ts
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
>     tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) m ty
>     return ty
> tcExpr m tcEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     tcExpr m tcEnv p e1 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m boolType
>     ty <- tcExpr m tcEnv p e2
>     tcExpr m tcEnv p e3 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>             m ty
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
>     tcConstrTerm m tcEnv noSigs p t >>=
>       unify p "case pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>             m tyLhs
>     tcRhs m tcEnv rhs >>= unify p "case branch" doc m tyRhs
>   where doc = ppAlt a

> tcQual :: ModuleIdent -> TCEnv -> Position -> Statement -> TcState ()
> tcQual m tcEnv p (StmtExpr e) =
>   tcExpr m tcEnv p e >>= unify p "guard" (ppExpr 0 e) m boolType
> tcQual m tcEnv p q@(StmtBind t e) =
>   do
>     ty <- tcConstrTerm m tcEnv noSigs p t
>     tcExpr m tcEnv p e >>=
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             m (listType ty)
> tcQual m tcEnv p (StmtDecl ds) = tcDecls m tcEnv ds

> tcStmt :: ModuleIdent -> TCEnv -> Position -> Statement -> TcState ()
> tcStmt m tcEnv p (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) m (ioType alpha)
> tcStmt m tcEnv p st@(StmtBind t e) =
>   do
>     ty <- tcConstrTerm m tcEnv noSigs p t
>     tcExpr m tcEnv p e >>=
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             m (ioType ty)
> tcStmt m tcEnv p (StmtDecl ds) = tcDecls m tcEnv ds

\end{verbatim}
The function \texttt{tcArrow} checks that its argument can be used as
an arrow type $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$. Similarly, the function \texttt{tcBinary} checks
that its argument can be used as an arrow type
$\alpha\rightarrow\beta\rightarrow\gamma$ and returns the triple
$(\alpha,\beta,\gamma)$.
\begin{verbatim}

> tcArrow :: Position -> String -> Doc -> ModuleIdent -> Type
>         -> TcState (Type,Type)
> tcArrow p what doc m ty =
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
>         unaryArrow ty = errorAt p (nonFunctionType what doc m ty)

> tcBinary :: Position -> String -> Doc -> ModuleIdent -> Type
>          -> TcState (Type,Type,Type)
> tcBinary p what doc m ty = tcArrow p what doc m ty >>= uncurry binaryArrow
>   where binaryArrow ty1 (TypeArrow ty2 ty3) = return (ty1,ty2,ty3)
>         binaryArrow ty1 (TypeVariable tv) =
>           do
>             beta <- freshTypeVar
>             gamma <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow beta gamma)))
>             return (ty1,beta,gamma)
>         binaryArrow ty1 ty2 =
>           errorAt p (nonBinaryOp what doc m (TypeArrow ty1 ty2))

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> ModuleIdent -> Type -> Type
>       -> TcState ()
> unify p what doc m ty1 ty2 =
>   liftSt $ {-$-}
>   do
>     theta <- fetchSt
>     let ty1' = subst theta ty1
>     let ty2' = subst theta ty2
>     either (errorAt p . typeMismatch what doc m ty1' ty2')
>            (updateSt_ . compose)
>            (unifyTypes m ty1' ty2')

> unifyTypes :: ModuleIdent -> Type -> Type -> Either Doc TypeSubst
> unifyTypes _ (TypeVariable tv1) (TypeVariable tv2)
>   | tv1 == tv2 = Right idSubst
>   | otherwise = Right (bindSubst tv1 (TypeVariable tv2) idSubst)
> unifyTypes m (TypeVariable tv) ty
>   | tv `elem` typeVars ty = Left (recursiveType m tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes m ty (TypeVariable tv)
>   | tv `elem` typeVars ty = Left (recursiveType m tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes _ (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2)
>   | tv1 == tv2 = Right idSubst
>   | tys1 == tys2 = Right (bindSubst tv1 (TypeConstrained tys2 tv2) idSubst)
> unifyTypes m (TypeConstrained tys tv) ty =
>   foldr (choose . unifyTypes m ty) (Left (incompatibleTypes m ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes m ty (TypeConstrained tys tv) =
>   foldr (choose . unifyTypes m ty) (Left (incompatibleTypes m ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes m (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = unifyTypeLists m tys1 tys2
> unifyTypes m (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   unifyTypeLists m [ty11,ty12] [ty21,ty22]
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Right idSubst
> unifyTypes m ty1 ty2 = Left (incompatibleTypes m ty1 ty2)

> unifyTypeLists :: ModuleIdent -> [Type] -> [Type] -> Either Doc TypeSubst
> unifyTypeLists _ [] _ = Right idSubst
> unifyTypeLists _ _ [] = Right idSubst
> unifyTypeLists m (ty1:tys1) (ty2:tys2) =
>   either Left (unifyTypesTheta m ty1 ty2) (unifyTypeLists m tys1 tys2)
>   where unifyTypesTheta m ty1 ty2 theta =
>           either Left (Right . flip compose theta)
>                  (unifyTypes m (subst theta ty1) (subst theta ty2))

\end{verbatim}
For each function declaration, the type checker ensures that no skolem
type escapes its scope. This is slightly more general than the
algorithm in~\cite{LauferOdersky94:AbstractTypes}, which checks for
escaping skolems at every let binding, but is still sound.
\begin{verbatim}

> checkSkolems :: Position -> ModuleIdent -> Doc -> ValueEnv -> Type
>              -> TcState Type
> checkSkolems p m what tyEnv ty =
>   do
>     theta <- liftSt fetchSt
>     let ty' = subst theta ty
>         fs = fsEnv (subst theta tyEnv)
>     unless (all (`elemSet` fs) (typeSkolems ty'))
>            (errorAt p (skolemEscapingScope m what ty'))
>     return ty'

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

> instExist :: ExistTypeScheme -> TcState Type
> instExist (ForAllExist n n' ty) =
>   do
>     tys <- replicateM (n + n') freshTypeVar
>     return (expandAliasType tys ty)

> skol :: ExistTypeScheme -> TcState Type
> skol (ForAllExist n n' ty) =
>   do
>     tys <- replicateM n freshTypeVar
>     tys' <- replicateM n' freshSkolem
>     return (expandAliasType (tys ++ tys') ty)

> gen :: Set Int -> Type -> TypeScheme
> gen gvs ty =
>   ForAll (length tvs) (subst (foldr2 bindSubst idSubst tvs tvs') ty)
>   where tvs = [tv | tv <- nub (typeVars ty), tv `notElemSet` gvs]
>         tvs' = map TypeVariable [0..]

> replicateM :: Monad m => Int -> m a -> m [a]
> replicateM n = sequence . replicate n

\end{verbatim}
\paragraph{Auxiliary Functions}
The functions \texttt{conType}, \texttt{varType}, and \texttt{funType}
are used to retrieve the type of constructors, pattern variables, and
variables in expressions, respectively, from the type environment.
Because the syntactical correctness has already been verified by the
syntax checker, none of these functions should fail.

Note that \texttt{varType} can handle ambiguous identifiers and
returns the first available type. This function is used for looking up
the type of an identifier on the left hand side of a rule where it
unambiguously refers to the local definition.
\begin{verbatim}

> conType :: QualIdent -> ValueEnv -> ExistTypeScheme
> conType c tyEnv =
>   case qualLookupValue c tyEnv of
>     [DataConstructor _ sigma] -> sigma
>     [NewtypeConstructor _ sigma] -> sigma
>     _ -> internalError ("conType " ++ show c)

> varType :: Ident -> ValueEnv -> TypeScheme
> varType v tyEnv =
>   case lookupValue v tyEnv of
>     Value _ sigma : _ -> sigma
>     _ -> internalError ("varType " ++ show v)

> funType :: QualIdent -> ValueEnv -> TypeScheme
> funType f tyEnv =
>   case qualLookupValue f tyEnv of
>     [Value _ sigma] -> sigma
>     _ -> internalError ("funType " ++ show f)

\end{verbatim}
The function \texttt{expandType} expands all type synonyms in a type
and also qualifies all type constructors with the name of the module
in which the type was defined.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs ty = expandType tcEnv (toType tvs ty)

> expandMonoTypes :: TCEnv -> [Ident] -> [TypeExpr] -> [Type]
> expandMonoTypes tcEnv tvs tys = map (expandType tcEnv) (toTypes tvs tys)

> expandPolyType :: TCEnv -> TypeExpr -> TypeScheme
> expandPolyType tcEnv ty = polyType $ normalize $ expandMonoType tcEnv [] ty

> expandType :: TCEnv -> Type -> Type
> expandType tcEnv (TypeConstructor tc tys) =
>   case qualLookupTC tc tcEnv of
>     [DataType tc' _ _] -> TypeConstructor tc' tys'
>     [RenamingType tc' _ _] -> TypeConstructor tc' tys'
>     [AliasType _ _ ty] -> expandAliasType tys' ty
>     _ -> internalError ("expandType " ++ show tc)
>   where tys' = map (expandType tcEnv) tys
> expandType _ (TypeVariable tv) = TypeVariable tv
> expandType _ (TypeConstrained tys tv) = TypeConstrained tys tv
> expandType tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (expandType tcEnv ty1) (expandType tcEnv ty2)
> expandType tcEnv (TypeSkolem k) = TypeSkolem k

\end{verbatim}
The functions \texttt{fvEnv} and \texttt{fsEnv} compute the set of
free type variables and free skolems of a type environment,
respectively. We ignore the types of data constructors here because we
know that they are closed.
\begin{verbatim}

> fvEnv :: ValueEnv -> Set Int
> fvEnv tyEnv =
>   fromListSet [tv | ty <- localTypes tyEnv, tv <- typeVars ty, tv < 0]

> fsEnv :: ValueEnv -> Set Int
> fsEnv tyEnv = unionSets (map (fromListSet . typeSkolems) (localTypes tyEnv))

> localTypes :: ValueEnv -> [Type]
> localTypes tyEnv = [ty | (_,Value _ (ForAll _ ty)) <- localBindings tyEnv]

\end{verbatim}
Error functions.
\begin{verbatim}

> recursiveTypes :: [Ident] -> String
> recursiveTypes [tc] = "Recursive synonym type " ++ name tc
> recursiveTypes (tc:tcs) =
>   "Recursive synonym types " ++ name tc ++ types "" tcs
>   where types comma [tc] = comma ++ " and " ++ name tc
>         types _ (tc:tcs) = ", " ++ name tc ++ types "," tcs

> polymorphicVar :: Ident -> String
> polymorphicVar v = "Variable " ++ name v ++ " cannot have polymorphic type"

> typeSigTooGeneral :: ModuleIdent -> Doc -> TypeExpr -> TypeScheme -> String
> typeSigTooGeneral m what ty sigma = show $
>   vcat [text "Type signature too general", what,
>         text "Inferred type:" <+> ppTypeScheme m sigma,
>         text "Type signature:" <+> ppTypeExpr 0 ty]

> nonFunctionType :: String -> Doc -> ModuleIdent -> Type -> String
> nonFunctionType what doc m ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType m ty,
>         text "Cannot be applied"]

> nonBinaryOp :: String -> Doc -> ModuleIdent -> Type -> String
> nonBinaryOp what doc m ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType m ty,
>         text "Cannot be used as binary operator"]

> typeMismatch :: String -> Doc -> ModuleIdent -> Type -> Type -> Doc -> String
> typeMismatch what doc m ty1 ty2 reason = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Inferred type:" <+> ppType m ty2,
>         text "Expected type:" <+> ppType m ty1,
>         reason]

> skolemEscapingScope :: ModuleIdent -> Doc -> Type -> String
> skolemEscapingScope m what ty = show $
>   vcat [text "Existential type escapes out of its scope", what,
>         text "Type:" <+> ppType m ty]

> invalidCType :: String -> ModuleIdent -> Type -> String
> invalidCType what m ty = show $
>   vcat [text ("Invalid " ++ what ++ " type in foreign declaration"),
>         ppType m ty]

> recursiveType :: ModuleIdent -> Int -> Type -> Doc
> recursiveType m tv ty = incompatibleTypes m (TypeVariable tv) ty

> incompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
> incompatibleTypes m ty1 ty2 =
>   sep [text "Types" <+> ppType m ty1,
>        nest 2 (text "and" <+> ppType m ty2),
>        text "are incompatible"]

\end{verbatim}
