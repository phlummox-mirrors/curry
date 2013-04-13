% -*- LaTeX -*-
% $Id: TypeCheck.lhs 3125 2013-04-13 14:39:29Z wlux $
%
% Copyright (c) 1999-2013, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeCheck.lhs}
\section{Type Inference}
This module implements the type checker of the Curry compiler. The
type checker is invoked after the syntactic correctness of the program
has been verified and kind checking has been applied to all type
expressions. Local variables have been renamed already. Therefore, the
compiler can maintain a flat type environment. The type checker now
checks the correct typing of all expressions and also verifies that
the type signatures given by the user match the inferred types. The
type checker uses algorithm W~\cite{DamasMilner82:Principal} for
inferring the types of unannotated declarations, but allows for
polymorphic recursion when a type annotation is present.

The result of type checking is a (flat) top-level environment
containing the types of all constructors, variables, and functions
defined at the top level of a module. In addition, a type annotated
source module or goal is returned. Note that type annotations on the
left hand side of a declaration hold the function or variable's
generalized type with the type scheme's for all qualifier left
implicit. Type annotations on the right hand side of a declaration
hold the particular instance at which a polymorphic function or
variable is used.
\begin{verbatim}

> module TypeCheck(typeCheck,typeCheckGoal) where
> import Base
> import Combined
> import Curry
> import CurryPP
> import CurryUtils
> import Env
> import Error
> import List
> import Monad
> import Position
> import PredefIdent
> import PredefTypes
> import Pretty
> import SCC
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeSubst
> import TypeTrans
> import Utils
> import ValueInfo

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
> typeCheck m tcEnv tyEnv ds = run $
>   do
>     tds' <- liftSt (liftSt (mapE (tcTopDecl tcEnv) tds))
>     (tyEnv'',vds') <- tcDecls m tcEnv tyEnv' [d | BlockDecl d <- vds]
>     theta <- fetchSt
>     return (subst theta tyEnv'',
>             tds' ++ map (BlockDecl . fmap (subst theta)) vds')
>   where (vds,tds) = partition isBlockDecl ds
>         tyEnv' = foldr (bindConstrs m tcEnv) tyEnv tds

\end{verbatim}
Type checking of a goal is simpler because there are no type
declarations.
\begin{verbatim}

> typeCheckGoal :: ModuleIdent -> TCEnv -> ValueEnv -> Goal a
>               -> Error (Goal Type)
> typeCheckGoal m tcEnv tyEnv g = run $
>   do
>     (_,g') <- tcGoal m tcEnv tyEnv g
>     theta <- fetchSt
>     return (fmap (subst theta) g')

\end{verbatim}
The type checker makes use of nested state monads in order to maintain
the current substitution and a counter, which is used for generating
fresh type variables.
\begin{verbatim}

> type TcState a = StateT TypeSubst (StateT Int Error) a

> run :: TcState a -> Error a
> run m = callSt (callSt m idSubst) 1

\end{verbatim}
\paragraph{Defining Data Constructors}
First, the types of all data and newtype constructors as well as those
of their field labels are entered into the type environment. All type
synonyms occurring in their types are expanded. We cannot use
\texttt{expandPolyType} for expanding the type of a data or newtype
constructor in function \texttt{bindConstr} because of the different
normalization scheme used for constructor types and also because the
name of the type could be ambiguous.
\begin{verbatim}

> bindConstrs :: ModuleIdent -> TCEnv -> TopDecl a -> ValueEnv -> ValueEnv
> bindConstrs m tcEnv (DataDecl _ tc tvs cs) tyEnv =
>   foldr bindCon (foldr (uncurry bindLab) tyEnv (nubBy sameLabel ls)) cs
>   where ty0 = constrType m tc tvs
>         ls = [(l,ty) | RecordDecl _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls]
>         bindCon (ConstrDecl _ _ c tys) =
>           bindConstr m tcEnv tvs c (zip (repeat anonId) tys) ty0
>         bindCon (ConOpDecl _ _ ty1 op ty2) =
>           bindConstr m tcEnv tvs op [(anonId,ty1),(anonId,ty2)] ty0
>         bindCon (RecordDecl _ _ c fs) = bindConstr m tcEnv tvs c tys ty0
>           where tys = [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls]
>         bindLab = bindLabel m tcEnv tvs ty0
>         sameLabel (l1,_) (l2,_) = l1 == l2
> bindConstrs m tcEnv (NewtypeDecl _ tc tvs nc) tyEnv = bind nc tyEnv
>   where ty0 = constrType m tc tvs
>         bind (NewConstrDecl _ c ty) =
>           bindNewConstr m tcEnv tvs c anonId ty ty0
>         bind (NewRecordDecl _ c l ty) =
>           bindNewConstr m tcEnv tvs c l ty ty0 .
>           bindLabel m tcEnv tvs ty0 l ty
> bindConstrs _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindConstrs _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: ModuleIdent -> TCEnv -> [Ident] -> Ident -> [(Ident,TypeExpr)]
>            -> Type -> ValueEnv -> ValueEnv
> bindConstr m tcEnv tvs c tys ty0 =
>   globalBindTopEnv m c (DataConstructor (qualifyWith m c) ls ty')
>   where ty' = polyType (normalize (length tvs) (foldr TypeArrow ty0 tys''))
>         tys'' = expandMonoTypes tcEnv tvs tys'
>         (ls,tys') = unzip tys

> bindNewConstr :: ModuleIdent -> TCEnv -> [Ident] -> Ident -> Ident -> TypeExpr
>               -> Type -> ValueEnv -> ValueEnv
> bindNewConstr m tcEnv tvs c l ty1 ty0 =
>   globalBindTopEnv m c (NewtypeConstructor (qualifyWith m c) l ty')
>   where ty' = polyType (normalize (length tvs) (TypeArrow ty1' ty0))
>         ty1' = expandMonoType tcEnv tvs ty1

> bindLabel :: ModuleIdent -> TCEnv -> [Ident] -> Type -> Ident -> TypeExpr
>           -> ValueEnv -> ValueEnv
> bindLabel m tcEnv tvs ty0 l ty =
>   globalBindTopEnv m l (Value (qualifyWith m l) 1 ty')
>   where ty' = polyType (TypeArrow ty0 (expandMonoType tcEnv tvs ty))

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
\paragraph{Top-level Declarations}
When a field label occurs in more than one constructor declaration of
a data type, the compiler ensures that the label is defined
consistently. In addition, the compiler ensures that no existentially
quantified type variable occurs in the type of a field label because
such type variables necessarily escape their scope with the type of
the record selection function associated with the field label.
\begin{verbatim}

> tcTopDecl :: TCEnv -> TopDecl a -> Error (TopDecl Type)
> tcTopDecl tcEnv (DataDecl p tc tvs cs) =
>   do
>     ls' <- mapE (uncurry (tcFieldLabel tcEnv tvs)) ls
>     mapE_ (uncurry tcFieldLabels) (groupLabels ls')
>     return (DataDecl p tc tvs cs)
>   where ls = [(P p l,ty) | RecordDecl _ _ _ fs <- cs,
>                            FieldDecl p ls ty <- fs, l <- ls]
> tcTopDecl _ (NewtypeDecl p tc tvs nc) = return (NewtypeDecl p tc tvs nc)
> tcTopDecl _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)

> tcFieldLabel :: TCEnv -> [Ident] -> P Ident -> TypeExpr
>              -> Error (P Ident,Type)
> tcFieldLabel tcEnv tvs (P p l) ty
>   | n <= length tvs = return (P p l,ty')
>   | otherwise = errorAt p (skolemFieldLabel l)
>   where ForAll n ty' = polyType (expandMonoType tcEnv tvs ty)

> tcFieldLabels :: P Ident -> [Type] -> Error ()
> tcFieldLabels (P p l) (ty:tys) =
>   unless (all (ty ==) tys) (errorAt p (inconsistentFieldLabel l))

> groupLabels :: Eq a => [(a,b)] -> [(a,[b])]
> groupLabels [] = []
> groupLabels ((x,y):xys) = (x,y:map snd xys') : groupLabels xys''
>   where (xys',xys'') = partition ((x ==) . fst) xys

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

> tcDecls :: ModuleIdent -> TCEnv -> ValueEnv -> [Decl a]
>         -> TcState (ValueEnv,[Decl Type])
> tcDecls m tcEnv tyEnv ds =
>   do
>     (tyEnv',dss') <-
>       mapAccumM (tcDeclGroup m tcEnv (foldr bindTypeSigs noSigs ods)) tyEnv
>                 (scc bv (qfv m) vds)
>     return (tyEnv',map untyped ods ++ concat dss')
>   where (vds,ods) = partition isValueDecl ds

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> ValueEnv -> [Decl a]
>             -> TcState (ValueEnv,[Decl Type])
> tcDeclGroup m tcEnv _ tyEnv [ForeignDecl p fi _ f ty] =
>   do
>     (tyEnv',ty') <- tcForeignFunct m tcEnv tyEnv p fi f ty
>     return (tyEnv',[ForeignDecl p fi ty' f ty])
> tcDeclGroup m tcEnv sigs tyEnv [FreeDecl p vs] =
>   do
>     vs' <- mapM (tcDeclVar False tcEnv sigs p) (bv vs)
>     return (bindVars m tyEnv vs',[FreeDecl p (map freeVar vs')])
>   where freeVar (v,_,ty) = FreeVar (rawType ty) v
> tcDeclGroup m tcEnv sigs tyEnv ds =
>   do
>     vss <- mapM (tcDeclVars tcEnv sigs) ds
>     let tyEnv' = bindVars m tyEnv (concat vss)
>     impDs' <- mapM (tcDecl m tcEnv tyEnv') impDs
>     theta <- fetchSt
>     let tvs =
>           [tv | (ty,d) <- impDs', not (isNonExpansive tcEnv tyEnv' d),
>                 tv <- typeVars (subst theta ty)]
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv)) tvs
>     let impDs'' = map (uncurry (fixType . gen fvs . subst theta)) impDs'
>         tyEnv'' = rebindVars m tyEnv' (concatMap declVars impDs'')
>     expDs' <- mapM (uncurry (tcCheckDecl m tcEnv tyEnv'')) expDs
>     return (tyEnv'',impDs'' ++ expDs')
>   where (impDs,expDs) = partDecls sigs ds

> partDecls :: SigEnv -> [Decl a] -> ([Decl a],[(TypeExpr,Decl a)])
> partDecls sigs =
>   foldr (\d -> maybe (implicit d) (explicit d) (declTypeSig sigs d)) ([],[])
>   where implicit d ~(impDs,expDs) = (d:impDs,expDs)
>         explicit d ty ~(impDs,expDs) = (impDs,(ty,d):expDs)

> declTypeSig :: SigEnv -> Decl a -> Maybe TypeExpr
> declTypeSig sigs (FunctionDecl _ _ f _) = lookupEnv f sigs
> declTypeSig sigs (PatternDecl _ t _) =
>   case t of
>     VariablePattern _ v -> lookupEnv v sigs
>     _ -> Nothing

> bindVars :: ModuleIdent -> ValueEnv -> [(Ident,Int,TypeScheme)] -> ValueEnv
> bindVars m = foldr (uncurry3 (bindFun m))

> rebindVars :: ModuleIdent -> ValueEnv -> [(Ident,Int,TypeScheme)] -> ValueEnv
> rebindVars m = foldr (uncurry3 (rebindFun m))

> tcDeclVars :: TCEnv -> SigEnv -> Decl a -> TcState [(Ident,Int,TypeScheme)]
> tcDeclVars tcEnv sigs (FunctionDecl _ _ f eqs) =
>   case lookupEnv f sigs of
>     Just ty -> return [(f,n,expandPolyType tcEnv ty)]
>     Nothing ->
>       do
>         tys <- replicateM (n + 1) freshTypeVar
>         return [(f,n,monoType (foldr1 TypeArrow tys))]
>   where n = eqnArity (head eqs)
> tcDeclVars tcEnv sigs (PatternDecl p t _) =
>   case t of
>     VariablePattern _ v -> mapM (tcDeclVar True tcEnv sigs p) [v]
>     _ -> mapM (tcDeclVar False tcEnv sigs p) (bv t)

> tcDeclVar :: Bool -> TCEnv -> SigEnv -> Position -> Ident
>           -> TcState (Ident,Int,TypeScheme)
> tcDeclVar poly tcEnv sigs p v =
>   case lookupEnv v sigs of
>     Just ty
>       | poly || null (fv ty) -> return (v,0,expandPolyType tcEnv ty)
>       | otherwise -> errorAt p (polymorphicVar v)
>     Nothing -> lambdaVar v

> tcDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Decl a
>        -> TcState (Type,Decl Type)
> tcDecl m tcEnv tyEnv (FunctionDecl p _ f eqs) =
>   do
>     theta <- fetchSt
>     ty <- inst (varType f tyEnv)
>     eqs' <-
>       mapM (tcEquation m tcEnv tyEnv (fsEnv (subst theta tyEnv)) ty f) eqs
>     return (ty,FunctionDecl p ty f eqs')
> tcDecl m tcEnv tyEnv d@(PatternDecl p t rhs) =
>   do
>     (ty,t') <- tcConstrTerm tcEnv tyEnv p t
>     rhs' <-
>       tcRhs m tcEnv tyEnv rhs >>-
>       unify p "pattern declaration" (ppDecl d) tcEnv ty
>     return (ty,PatternDecl p t' rhs')

> tcEquation :: ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Type -> Ident
>            -> Equation a -> TcState (Equation Type)
> tcEquation m tcEnv tyEnv fs ty f eq@(Equation p lhs rhs) =
>   tcEqn m tcEnv tyEnv fs p lhs rhs >>-
>   unify p "equation" (ppEquation eq) tcEnv ty

> tcEqn :: ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Position
>       -> Lhs a -> Rhs a -> TcState (Type,Equation Type)
> tcEqn m tcEnv tyEnv fs p lhs rhs =
>   do
>     tyEnv' <- bindLambdaVars m tyEnv lhs
>     (tys,lhs') <- tcLhs tcEnv tyEnv' p lhs
>     (ty,rhs') <- tcRhs m tcEnv tyEnv' rhs
>     checkSkolems p "Equation" ppEquation tcEnv tyEnv fs
>                  (foldr TypeArrow ty tys) (Equation p lhs' rhs')

> bindLambdaVars :: QuantExpr t => ModuleIdent -> ValueEnv -> t
>                -> TcState ValueEnv
> bindLambdaVars m tyEnv t = liftM (bindVars m tyEnv) (mapM lambdaVar (bv t))

> lambdaVar :: Ident -> TcState (Ident,Int,TypeScheme)
> lambdaVar v = freshTypeVar >>= \ty -> return (v,0,monoType ty)

> tcGoal :: ModuleIdent -> TCEnv -> ValueEnv -> Goal a
>        -> TcState (Type,Goal Type)
> tcGoal m tcEnv tyEnv (Goal p e ds) =
>   do
>     (tyEnv',ds') <- tcDecls m tcEnv tyEnv ds
>     (ty,e') <- tcExpr m tcEnv tyEnv' p e
>     checkSkolems p "Goal" ppGoal tcEnv tyEnv zeroSet ty (Goal p e' ds')

\end{verbatim}
After \texttt{tcDeclGroup} has generalized the types of the implicitly
typed declarations of a declaration group it must update their left
hand side type annotations and the type environment accordingly.
Recall that the compiler generalizes only the types of variable and
function declarations.
\begin{verbatim}

> fixType :: TypeScheme -> Decl Type -> Decl Type
> fixType ty (FunctionDecl p _ f eqs) = FunctionDecl p (rawType ty) f eqs
> fixType ty (PatternDecl p t rhs) = PatternDecl p (fixVarType ty t) rhs
>   where fixVarType ty t =
>           case t of
>             VariablePattern _ v -> VariablePattern (rawType ty) v
>             _ -> t

> declVars :: Decl Type -> [(Ident,Int,TypeScheme)]
> declVars (FunctionDecl _ ty f eqs) = [(f,eqnArity (head eqs),polyType ty)]
> declVars (PatternDecl _ t _) =
>   case t of
>     VariablePattern ty v -> [(v,0,polyType ty)]
>     _ -> []

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
>     (ty,d') <- tcDecl m tcEnv tyEnv d
>     theta <- fetchSt
>     let fvs = fvEnv (subst theta tyEnv)
>         ty' = subst theta ty
>     checkDeclSig tcEnv sigTy (if poly then gen fvs ty' else monoType ty') d'
>   where poly = isNonExpansive tcEnv tyEnv d

> checkDeclSig :: TCEnv -> TypeExpr -> TypeScheme -> Decl Type
>              -> TcState (Decl Type)
> checkDeclSig tcEnv sigTy sigma (FunctionDecl p _ f eqs)
>   | sigma == expandPolyType tcEnv sigTy =
>       return (FunctionDecl p (rawType sigma) f eqs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Function:" <+> ppIdent f
> checkDeclSig tcEnv sigTy sigma (PatternDecl p (VariablePattern _ v) rhs)
>   | sigma == expandPolyType tcEnv sigTy =
>       return (PatternDecl p (VariablePattern (rawType sigma) v) rhs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Variable:" <+> ppIdent v

> class Binding a where
>   isNonExpansive :: TCEnv -> ValueEnv -> a -> Bool

> instance Binding a => Binding [a] where
>   isNonExpansive tcEnv tyEnv = all (isNonExpansive tcEnv tyEnv)

> instance Binding (Decl a) where
>   isNonExpansive _ _ (InfixDecl _ _ _ _) = True
>   isNonExpansive _ _ (TypeSig _ _ _) = True
>   isNonExpansive _ _ (FunctionDecl _ _ _ _) = True
>   isNonExpansive _ _ (ForeignDecl _ _ _ _ _) = True
>   isNonExpansive tcEnv tyEnv (PatternDecl _ t rhs) =
>     isVariablePattern t && isNonExpansive tcEnv tyEnv rhs
>   isNonExpansive _ _ (FreeDecl _ _) = False
>   isNonExpansive _ _ (TrustAnnot _ _ _) = True

> instance Binding (Rhs a) where
>   isNonExpansive tcEnv tyEnv (SimpleRhs _ e ds) =
>     isNonExpansive tcEnv tyEnv' ds && isNonExpansive tcEnv tyEnv' e
>     where tyEnv' = foldr (bindDeclArity tcEnv) tyEnv ds
>   isNonExpansive _ _ (GuardedRhs _ _) = False

> instance Binding (Expression a) where
>   isNonExpansive tcEnv tyEnv = isNonExpansiveApp tcEnv tyEnv 0

> instance Binding a => Binding (Field a) where
>   isNonExpansive tcEnv tyEnv (Field _ e) = isNonExpansive tcEnv tyEnv e

> isNonExpansiveApp :: TCEnv -> ValueEnv -> Int -> Expression a -> Bool
> isNonExpansiveApp _ _ _ (Literal _ _) = True
> isNonExpansiveApp _ tyEnv n (Variable _ v)
>   | unqualify v == anonId = False
>   | isRenamed (unqualify v) = n == 0 || n < arity v tyEnv
>   | otherwise = n < arity v tyEnv
> isNonExpansiveApp _ _ _ (Constructor _ _) = True
> isNonExpansiveApp tcEnv tyEnv n (Paren e) = isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv n (Typed e _) =
>   isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv _ (Record _ _ fs) =
>   isNonExpansive tcEnv tyEnv fs
>   -- FIXME: stricly speaking a record construction is non-expansive
>   -- only if *all* field labels are present; for instance, (:){}
>   -- probably should be considered expansive
> isNonExpansiveApp tcEnv tyEnv _ (Tuple es) = isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv _ (List _ es) = isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv n (Apply f e) =
>   isNonExpansiveApp tcEnv tyEnv (n + 1) f && isNonExpansive tcEnv tyEnv e
> isNonExpansiveApp tcEnv tyEnv n (InfixApply e1 op e2) =
>   isNonExpansiveApp tcEnv tyEnv (n + 2) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e1 && isNonExpansive tcEnv tyEnv e2
> isNonExpansiveApp tcEnv tyEnv n (LeftSection e op) =
>   isNonExpansiveApp tcEnv tyEnv (n + 1) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e
> isNonExpansiveApp tcEnv tyEnv n (Lambda _ ts e) =
>   n < length ts ||
>   all isVarPattern ts && isNonExpansiveApp tcEnv tyEnv' (n - length ts) e
>   where tyEnv' = foldr bindVarArity tyEnv (bv ts)
> isNonExpansiveApp tcEnv tyEnv n (Let ds e) =
>   isNonExpansive tcEnv tyEnv' ds && isNonExpansiveApp tcEnv tyEnv' n e
>   where tyEnv' = foldr (bindDeclArity tcEnv) tyEnv ds
> isNonExpansiveApp _ _ _ _ = False

> bindDeclArity :: TCEnv -> Decl a -> ValueEnv -> ValueEnv
> bindDeclArity _ (InfixDecl _ _ _ _) tyEnv = tyEnv
> bindDeclArity _ (TypeSig _ _ _) tyEnv = tyEnv
> bindDeclArity _ (FunctionDecl _ _ f eqs) tyEnv =
>   bindArity f (eqnArity (head eqs)) tyEnv
> bindDeclArity tcEnv (ForeignDecl _ _ _ f ty) tyEnv =
>   bindArity f (foreignArity (rawType (expandPolyType tcEnv ty))) tyEnv
> bindDeclArity _ (PatternDecl _ t _) tyEnv = foldr bindVarArity tyEnv (bv t)
> bindDeclArity _ (FreeDecl _ vs) tyEnv = foldr bindVarArity tyEnv (bv vs)
> bindDeclArity _ (TrustAnnot _ _ _) tyEnv = tyEnv

> bindVarArity :: Ident -> ValueEnv -> ValueEnv
> bindVarArity v tyEnv = bindArity v 0 tyEnv

> bindArity :: Ident -> Int -> ValueEnv -> ValueEnv
> bindArity v n tyEnv = localBindTopEnv v (Value (qualify v) n undefined) tyEnv

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

> tcForeignFunct :: ModuleIdent -> TCEnv -> ValueEnv
>                -> Position -> ForeignImport -> Ident -> TypeExpr
>                -> TcState (ValueEnv,Type)
> tcForeignFunct m tcEnv tyEnv p (cc,_,ie) f ty =
>   do
>     checkForeignType cc ty'
>     return (bindFun m f (foreignArity ty') (ForAll n ty') tyEnv,ty')
>   where ForAll n ty' = expandPolyType tcEnv ty
>         checkForeignType cc ty
>           | cc == CallConvPrimitive = return ()
>           | ie == Just "dynamic" = checkCDynCallType tcEnv p cc ty
>           | maybe False ('&' `elem`) ie = checkCAddrType tcEnv p ty
>           | otherwise = checkCCallType tcEnv p cc ty

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

> tcLhs :: TCEnv -> ValueEnv -> Position -> Lhs a -> TcState ([Type],Lhs Type)
> tcLhs tcEnv tyEnv p (FunLhs f ts) =
>   do
>     (tys,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv tyEnv p) ts
>     return (tys,FunLhs f ts')
> tcLhs tcEnv tyEnv p (OpLhs t1 op t2) =
>   do
>     (ty1,t1') <- tcConstrTerm tcEnv tyEnv p t1
>     (ty2,t2') <- tcConstrTerm tcEnv tyEnv p t2
>     return ([ty1,ty2],OpLhs t1' op t2')
> tcLhs tcEnv tyEnv p (ApLhs lhs ts) =
>   do
>     (tys1,lhs') <- tcLhs tcEnv tyEnv p lhs
>     (tys2,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv tyEnv p) ts
>     return (tys1 ++ tys2,ApLhs lhs' ts')

> tcConstrTerm :: TCEnv -> ValueEnv -> Position -> ConstrTerm a
>              -> TcState (Type,ConstrTerm Type)
> tcConstrTerm _ _ _ (LiteralPattern _ l) =
>   do
>     ty <- tcLiteral l
>     return (ty,LiteralPattern ty l)
> tcConstrTerm _ _ _ (NegativePattern _ op l) =
>   do
>     ty <- tcLiteral l
>     return (ty,NegativePattern ty op l)
> tcConstrTerm _ tyEnv _ (VariablePattern _ v) =
>   do
>     ty <- inst (varType v tyEnv)
>     return (ty,VariablePattern ty v)
> tcConstrTerm tcEnv tyEnv p t@(ConstructorPattern _ c ts) =
>   do
>     ty <- skol (snd (conType c tyEnv))
>     tcConstrApp tcEnv tyEnv p (ppConstrTerm 0 t) c ty ts
> tcConstrTerm tcEnv tyEnv p t@(FunctionPattern _ f ts) =
>   do
>     ty <- inst (funType f tyEnv)
>     tcFunctPattern tcEnv tyEnv p (ppConstrTerm 0 t) f id ty ts
> tcConstrTerm tcEnv tyEnv p t@(InfixPattern _ t1 op t2) =
>   do
>     ty <- tcPatternOp tyEnv p op
>     (alpha,beta,gamma) <-
>       tcBinary p "infix pattern" (doc $-$ text "Operator:" <+> ppOp op)
>                tcEnv ty
>     t1' <- tcConstrArg tcEnv tyEnv p doc t1 alpha
>     t2' <- tcConstrArg tcEnv tyEnv p doc t2 beta
>     return (gamma,InfixPattern gamma t1' op t2')
>   where doc = ppConstrTerm 0 t
> tcConstrTerm tcEnv tyEnv p (ParenPattern t) =
>   do
>     (ty,t') <- tcConstrTerm tcEnv tyEnv p t
>     return (ty,ParenPattern t')
> tcConstrTerm tcEnv tyEnv p t@(RecordPattern _ c fs) =
>   do
>     ty <- liftM arrowBase (skol (snd (conType c tyEnv)))
>     fs' <- mapM (tcField tcConstrTerm "pattern" doc tcEnv tyEnv p ty) fs
>     return (ty,RecordPattern ty c fs')
>   where doc t1 = ppConstrTerm 0 t $-$ text "Term:" <+> ppConstrTerm 0 t1
> tcConstrTerm tcEnv tyEnv p (TuplePattern ts) =
>   do
>     (tys,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv tyEnv p) ts
>     return (tupleType tys,TuplePattern ts')
> tcConstrTerm tcEnv tyEnv p t@(ListPattern _ ts) =
>   do
>     ty <- freshTypeVar
>     ts' <- mapM (tcElem (ppConstrTerm 0 t) ty) ts
>     return (listType ty,ListPattern (listType ty) ts')
>   where tcElem doc ty t =
>           tcConstrTerm tcEnv tyEnv p t >>-
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 tcEnv ty
> tcConstrTerm tcEnv tyEnv p t@(AsPattern v t') =
>   do
>     ty <- inst (varType v tyEnv)
>     t'' <-
>       tcConstrTerm tcEnv tyEnv p t' >>-
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv ty
>     return (ty,AsPattern v t'')
> tcConstrTerm tcEnv tyEnv p (LazyPattern t) =
>   do
>     (ty,t') <- tcConstrTerm tcEnv tyEnv p t
>     return (ty,LazyPattern t')

> tcConstrApp :: TCEnv -> ValueEnv -> Position -> Doc -> QualIdent -> Type
>             -> [ConstrTerm a] -> TcState (Type,ConstrTerm Type)
> tcConstrApp tcEnv tyEnv p doc c ty ts =
>   do
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     ts' <- zipWithM (tcConstrArg tcEnv tyEnv p doc) ts tys
>     return (ty',ConstructorPattern ty' c ts')
>   where (tys,ty') = arrowUnapply ty
>         n = length ts

> tcFunctPattern :: TCEnv -> ValueEnv -> Position -> Doc -> QualIdent
>                -> ([ConstrTerm Type] -> [ConstrTerm Type]) -> Type
>                -> [ConstrTerm a] -> TcState (Type,ConstrTerm Type)
> tcFunctPattern _ _ _ _ f ts ty [] = return (ty,FunctionPattern ty f (ts []))
> tcFunctPattern tcEnv tyEnv p doc f ts ty (t':ts') =
>   do
>     (alpha,beta) <-
>       tcArrow p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv ty
>     t'' <- tcConstrArg tcEnv tyEnv p doc t' alpha
>     tcFunctPattern tcEnv tyEnv p doc f (ts . (t'':)) beta ts'
>   where t = FunctionPattern ty f (ts [])

> tcConstrArg :: TCEnv -> ValueEnv -> Position -> Doc -> ConstrTerm a -> Type
>             -> TcState (ConstrTerm Type)
> tcConstrArg tcEnv tyEnv p doc t ty =
>   tcConstrTerm tcEnv tyEnv p t >>-
>   unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv ty

> tcPatternOp :: ValueEnv -> Position -> InfixOp a -> TcState Type
> tcPatternOp tyEnv p (InfixConstr _ op) =
>   do
>     ty <- skol (snd (conType op tyEnv))
>     unless (arrowArity ty == 2) (errorAt p (wrongArity op (arrowArity ty) 2))
>     return ty
> tcPatternOp tyEnv _ (InfixOp _ op) = inst (funType op tyEnv)

> tcRhs :: ModuleIdent -> TCEnv -> ValueEnv -> Rhs a -> TcState (Type,Rhs Type)
> tcRhs m tcEnv tyEnv (SimpleRhs p e ds) =
>   do
>     (tyEnv',ds') <- tcDecls m tcEnv tyEnv ds
>     (ty,e') <- tcExpr m tcEnv tyEnv' p e
>     return (ty,SimpleRhs p e' ds')
> tcRhs m tcEnv tyEnv (GuardedRhs es ds) =
>   do
>     (tyEnv',ds') <- tcDecls m tcEnv tyEnv ds
>     gty <- guardType es
>     ty <- freshTypeVar
>     es' <- mapM (tcCondExpr m tcEnv tyEnv' gty ty) es
>     return (ty,GuardedRhs es' ds')
>   where guardType es
>           | length es > 1 = return boolType
>           | otherwise = freshConstrained [successType,boolType]

> tcCondExpr :: ModuleIdent -> TCEnv -> ValueEnv -> Type -> Type -> CondExpr a
>            -> TcState (CondExpr Type)
> tcCondExpr m tcEnv tyEnv gty ty (CondExpr p g e) =
>   do
>     g' <- tcExpr m tcEnv tyEnv p g >>- unify p "guard" (ppExpr 0 g) tcEnv gty
>     e' <-
>       tcExpr m tcEnv tyEnv p e >>- unify p "expression" (ppExpr 0 e) tcEnv ty
>     return (CondExpr p g' e')

> tcExpr :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> Expression a
>        -> TcState (Type,Expression Type)
> tcExpr _ _ _ _ (Literal _ l) =
>   do
>     ty <- tcLiteral l
>     return (ty,Literal ty l)
> tcExpr _ _ tyEnv _ (Variable _ v) =
>   do
>     ty <- if unRenameIdent (unqualify v) == anonId then freshTypeVar
>           else inst (funType v tyEnv)
>     return (ty,Variable ty v)
> tcExpr _ _ tyEnv _ (Constructor _ c) =
>   do
>     ty <- inst (snd (conType c tyEnv))
>     return (ty,Constructor ty c)
> tcExpr m tcEnv tyEnv p (Typed e sig) =
>   do
>     ty <- inst sigma'
>     e' <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "explicitly typed expression" (ppExpr 0 e) tcEnv ty
>     theta <- fetchSt
>     let sigma = gen (fvEnv (subst theta tyEnv)) (subst theta ty)
>     unless (sigma == sigma')
>       (errorAt p (typeSigTooGeneral tcEnv (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return (ty,Typed e' sig)
>   where sigma' = expandPolyType tcEnv sig
> tcExpr m tcEnv tyEnv p (Paren e) =
>   do
>     (ty,e') <- tcExpr m tcEnv tyEnv p e
>     return (ty,Paren e')
> tcExpr m tcEnv tyEnv p e@(Record _ c fs) =
>   do
>     ty <- liftM arrowBase (inst (snd (conType c tyEnv)))
>     fs' <- mapM (tcField (tcExpr m) "construction" doc tcEnv tyEnv p ty) fs
>     return (ty,Record ty c fs')
>   where doc e1 = ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1
> tcExpr m tcEnv tyEnv p e@(RecordUpdate e1 fs) =
>   do
>     (ty,e1') <- tcExpr m tcEnv tyEnv p e1
>     fs' <- mapM (tcField (tcExpr m) "update" doc tcEnv tyEnv p ty) fs
>     return (ty,RecordUpdate e1' fs')
>   where doc e1 = ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1
> tcExpr m tcEnv tyEnv p (Tuple es) =
>   do
>     (tys,es') <- liftM unzip $ mapM (tcExpr m tcEnv tyEnv p) es
>     return (tupleType tys,Tuple es')
> tcExpr m tcEnv tyEnv p e@(List _ es) =
>   do
>     ty <- freshTypeVar
>     es' <- mapM (tcElem (ppExpr 0 e) ty) es
>     return (listType ty,List (listType ty) es')
>   where tcElem doc ty e =
>           tcExpr m tcEnv tyEnv p e >>-
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e) tcEnv ty
> tcExpr m tcEnv tyEnv p (ListCompr e qs) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     (tyEnv',qs') <- mapAccumM (flip (tcQual m tcEnv) p) tyEnv qs
>     (ty,e') <- tcExpr m tcEnv tyEnv' p e
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs
>                  (listType ty) (ListCompr e' qs')
> tcExpr m tcEnv tyEnv p e@(EnumFrom e1) =
>   do
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     return (listType intType,EnumFrom e1')
> tcExpr m tcEnv tyEnv p e@(EnumFromThen e1 e2) =
>   do
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     e2' <-
>       tcExpr m tcEnv tyEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     return (listType intType,EnumFromThen e1' e2')
> tcExpr m tcEnv tyEnv p e@(EnumFromTo e1 e2) =
>   do
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     e2' <-
>       tcExpr m tcEnv tyEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     return (listType intType,EnumFromTo e1' e2')
> tcExpr m tcEnv tyEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv intType
>     e2' <-
>       tcExpr m tcEnv tyEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv intType
>     e3' <-
>       tcExpr m tcEnv tyEnv p e3 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) tcEnv intType
>     return (listType intType,EnumFromThenTo e1' e2' e3')
> tcExpr m tcEnv tyEnv p e@(UnaryMinus op e1) =
>   do
>     ty <- opType op
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv ty
>     return (ty,UnaryMinus op e1')
>   where opType op
>           | op == minusId = freshConstrained [intType,floatType]
>           | op == fminusId = return floatType
>           | otherwise = internalError ("tcExpr unary " ++ name op)
> tcExpr m tcEnv tyEnv p e@(Apply e1 e2) =
>   do
>     ((alpha,beta),e1') <-
>       tcExpr m tcEnv tyEnv p e1 >>=-
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>               tcEnv
>     e2' <-
>       tcExpr m tcEnv tyEnv p e2 >>-
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             tcEnv alpha
>     return (beta,Apply e1' e2')
> tcExpr m tcEnv tyEnv p e@(InfixApply e1 op e2) =
>   do
>     ((alpha,beta,gamma),op') <-
>       tcInfixOp tyEnv op >>=-
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv alpha
>     e2' <-
>       tcExpr m tcEnv tyEnv p e2 >>-
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv beta
>     return (gamma,InfixApply e1' op' e2')
> tcExpr m tcEnv tyEnv p e@(LeftSection e1 op) =
>   do
>     ((alpha,beta),op') <-
>       tcInfixOp tyEnv op >>=-
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               tcEnv
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv alpha
>     return (beta,LeftSection e1' op')
> tcExpr m tcEnv tyEnv p e@(RightSection op e1) =
>   do
>     ((alpha,beta,gamma),op') <-
>       tcInfixOp tyEnv op >>=-
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv beta
>     return (TypeArrow alpha gamma,RightSection op' e1')
> tcExpr m tcEnv tyEnv _ (Lambda p ts e) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     tyEnv' <- bindLambdaVars m tyEnv ts
>     (tys,ts') <- liftM unzip $ mapM (tcConstrTerm tcEnv tyEnv' p) ts
>     (ty,e') <- tcExpr m tcEnv tyEnv' p e
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs
>                  (foldr TypeArrow ty tys) (Lambda p ts' e')
> tcExpr m tcEnv tyEnv p (Let ds e) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     (tyEnv',ds') <- tcDecls m tcEnv tyEnv ds
>     (ty,e') <- tcExpr m tcEnv tyEnv' p e
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs ty (Let ds' e')
> tcExpr m tcEnv tyEnv p (Do sts e) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     (tyEnv',sts') <- mapAccumM (flip (tcStmt m tcEnv) p) tyEnv sts
>     ty <- liftM ioType freshTypeVar
>     e' <-
>       tcExpr m tcEnv tyEnv' p e >>- unify p "statement" (ppExpr 0 e) tcEnv ty
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs ty (Do sts' e')
> tcExpr m tcEnv tyEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     e1' <-
>       tcExpr m tcEnv tyEnv p e1 >>-
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv boolType
>     (ty,e2') <- tcExpr m tcEnv tyEnv p e2
>     e3' <-
>       tcExpr m tcEnv tyEnv p e3 >>-
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>             tcEnv ty
>     return (ty,IfThenElse e1' e2' e3')
> tcExpr m tcEnv tyEnv p (Case e as) =
>   do
>     (tyLhs,e') <- tcExpr m tcEnv tyEnv p e
>     tyRhs <- freshTypeVar
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     as' <- mapM (tcAlt m tcEnv tyEnv fs tyLhs tyRhs) as
>     return (tyRhs,Case e' as')
> tcExpr m tcEnv tyEnv p (Fcase e as) =
>   do
>     (tyLhs,e') <- tcExpr m tcEnv tyEnv p e
>     tyRhs <- freshTypeVar
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     as' <- mapM (tcAlt m tcEnv tyEnv fs tyLhs tyRhs) as
>     return (tyRhs,Fcase e' as')

> tcAlt :: ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Type -> Type -> Alt a
>       -> TcState (Alt Type)
> tcAlt m tcEnv tyEnv fs tyLhs tyRhs a@(Alt p t rhs) =
>   tcAltern m tcEnv tyEnv fs tyLhs tyRhs p t rhs >>- 
>   unify p "case alternative" (ppAlt a) tcEnv tyRhs

> tcAltern :: ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Type -> Type
>          -> Position -> ConstrTerm a -> Rhs a -> TcState (Type,Alt Type)
> tcAltern m tcEnv tyEnv fs tyLhs tyRhs p t rhs =
>   do
>     tyEnv' <- bindLambdaVars m tyEnv t
>     t' <-
>       tcConstrTerm tcEnv tyEnv' p t >>- unify p "case pattern" doc tcEnv tyLhs
>     (ty',rhs') <- tcRhs m tcEnv tyEnv' rhs
>     checkSkolems p "Alternative" ppAlt tcEnv tyEnv fs ty' (Alt p t' rhs')
>   where doc = ppAlt (Alt p t rhs) $-$ text "Term:" <+> ppConstrTerm 0 t

> tcQual :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> Statement a
>        -> TcState (ValueEnv,Statement Type)
> tcQual m tcEnv tyEnv p (StmtExpr e) =
>   do
>     e' <-
>       tcExpr m tcEnv tyEnv p e >>- unify p "guard" (ppExpr 0 e) tcEnv boolType
>     return (tyEnv,StmtExpr e')
> tcQual m tcEnv tyEnv _ q@(StmtBind p t e) =
>   do
>     alpha <- freshTypeVar
>     e' <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (listType alpha)
>     tyEnv' <- bindLambdaVars m tyEnv t
>     t' <-
>       tcConstrTerm tcEnv tyEnv' p t >>-
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppConstrTerm 0 t)
>             tcEnv alpha
>     return (tyEnv',StmtBind p t' e')
> tcQual m tcEnv tyEnv _ (StmtDecl ds) =
>   do
>     (tyEnv',ds') <- tcDecls m tcEnv tyEnv ds
>     return (tyEnv',StmtDecl ds')

> tcStmt :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> Statement a
>        -> TcState (ValueEnv,Statement Type)
> tcStmt m tcEnv tyEnv p (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     e' <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "statement" (ppExpr 0 e) tcEnv (ioType alpha)
>     return (tyEnv,StmtExpr e')
> tcStmt m tcEnv tyEnv _ st@(StmtBind p t e) =
>   do
>     alpha <- freshTypeVar
>     e' <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (ioType alpha)
>     tyEnv' <- bindLambdaVars m tyEnv t
>     t' <-
>       tcConstrTerm tcEnv tyEnv' p t >>-
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppConstrTerm 0 t)
>             tcEnv alpha
>     return (tyEnv',StmtBind p t' e')
> tcStmt m tcEnv tyEnv _ (StmtDecl ds) =
>   do
>     (tyEnv',ds') <- tcDecls m tcEnv tyEnv ds
>     return (tyEnv',StmtDecl ds')

> tcInfixOp :: ValueEnv -> InfixOp a -> TcState (Type,InfixOp Type)
> tcInfixOp tyEnv (InfixOp _ op) =
>   do
>     ty <- inst (funType op tyEnv)
>     return (ty,InfixOp ty op)
> tcInfixOp tyEnv (InfixConstr a op) =
>   do
>     ty <- inst (snd (conType op tyEnv))
>     return (ty,InfixConstr ty op)

> tcField :: (TCEnv -> ValueEnv -> Position -> a b -> TcState (Type,a Type))
>         -> String -> (a b -> Doc) -> TCEnv -> ValueEnv -> Position -> Type
>         -> Field (a b) -> TcState (Field (a Type))
> tcField tc what doc tcEnv tyEnv p ty (Field l x) =
>   do
>     TypeArrow ty1 ty2 <- inst (funType l tyEnv)
>     -- NB the following unification cannot fail; it serves only for
>     --    instantiating the type variables in the field label's type
>     unify p "field label" empty tcEnv ty ty1
>     x' <- tc tcEnv tyEnv p x >>- unify p ("record " ++ what) (doc x) tcEnv ty2
>     return (Field l x')

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
>     theta <- fetchSt
>     unaryArrow (subst theta ty)
>   where unaryArrow (TypeArrow ty1 ty2) = return (ty1,ty2)
>         unaryArrow (TypeVariable tv) =
>           do
>             alpha <- freshTypeVar
>             beta <- freshTypeVar
>             updateSt_ (bindVar tv (TypeArrow alpha beta))
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
>             updateSt_ (bindVar tv (TypeArrow beta gamma))
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
Whenever type inference succeeds for a function equation, $($f$)$case
alternative, etc., which may open an existentially quantified data
type and thus bring fresh skolem constants into scope the compiler
checks that none of those skolem constants escape their scope through
the result type or the type environment. E.g., for the sample program
\begin{verbatim}
  data Key a = forall b. b (b -> a)
  f (Key x _) = x 
  g k x = fcase k of { Key _ f -> f x }
\end{verbatim}
a skolem constant escapes in the (result) type of \texttt{f} and in
the type of the environment variable \texttt{x} for the fcase
expression in the definition of \texttt{g}
(cf.~\cite{LauferOdersky94:AbstractTypes}).
\begin{verbatim}

> checkSkolems :: Position -> String -> (a -> Doc) -> TCEnv -> ValueEnv
>              -> Set Int -> Type -> a -> TcState (Type,a)
> checkSkolems p what pp tcEnv tyEnv fs ty x =
>   do
>     theta <- fetchSt
>     let esc = filter escape [(v,subst theta ty) | (v,ty) <- (empty,ty) : tys]
>     unless (null esc) (errorAt p (skolemEscapingScope tcEnv what (pp x) esc))
>     return (ty,x)
>   where tys = [(var v,rawType ty) | (v,Value _ _ ty) <- localBindings tyEnv]
>         escape = any (`notElemSet` fs) . typeSkolems . snd
>         var v = text "Variable:" <+> ppIdent v

\end{verbatim}
\paragraph{Instantiation and Generalization}
We use negative offsets for fresh type variables.
\begin{verbatim}

> fresh :: (Int -> a) -> TcState a
> fresh f = liftM f (liftSt (updateSt (1 +)))

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

> inconsistentFieldLabel :: Ident -> String
> inconsistentFieldLabel l =
>   "Types for field label " ++ name l ++ " do not agree"

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

> skolemFieldLabel :: Ident -> String
> skolemFieldLabel l =
>   "Existential type escapes with type of record selector " ++ name l

> skolemEscapingScope :: TCEnv -> String -> Doc -> [(Doc,Type)] -> String
> skolemEscapingScope tcEnv what doc esc = show $ vcat $
>   text "Existential type escapes out of its scope" :
>   sep [text what <> colon,indent doc] :
>   [whence $$ text "Type:" <+> ppType tcEnv ty | (whence,ty) <- esc]

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
