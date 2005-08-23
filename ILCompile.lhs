% -*- LaTeX -*-
% $Id: ILCompile.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILCompile.lhs}
\section{Compiling the Intermediate Language}
This section describes the transformation from the intermediate
language into abstract machine code.
\begin{verbatim}

> module ILCompile where
> import Ident
> import IL
> import qualified Cam
> import Env
> import List
> import Map
> import Maybe
> import Monad
> import SCC
> import Combined
> import Utils

> type CompState a = StateT [Cam.Name] Id a

> camCompile :: Module -> Cam.Module
> camCompile (Module m is ds) =
>   map compileImport is ++ concat (map compileDecl ds)
>   where compileImport = Cam.ImportDecl . Cam.mangle . moduleName

> camCompileData :: [Decl] -> [Cam.Decl]
> camCompileData ds = [compileData tc cs | DataDecl tc _ cs <- ds]

> compileDecl :: Decl -> [Cam.Decl]
> compileDecl (DataDecl tc _ cs) = [compileData tc cs]
> compileDecl (NewtypeDecl _ _ _) = []
> compileDecl (FunctionDecl f vs _ e) = [compileFun f vs e]
> compileDecl (ForeignDecl f cc ie ty) = compileForeign f cc ie ty

> compileData :: QualIdent -> [ConstrDecl [Type]] -> Cam.Decl
> compileData tc cs = Cam.DataDecl (con tc) (map compileConstr cs)

> compileConstr :: ConstrDecl [Type] -> Cam.ConstrDecl
> compileConstr (ConstrDecl c tys)
>   | c == hidden = Cam.ConstrDecl hiddenCon 0
>   | otherwise = Cam.ConstrDecl (con c) (length tys)

> compileFun :: QualIdent -> [Ident] -> Expression -> Cam.Decl
> compileFun f vs e =
>   runSt (compile (Cam.FunctionDecl (fun f)) vs e) (nameSupply "_")
>   where compile = if isQSelectorId f then compileSelector else compileFunction
>         compileFunction f vs e =
>           liftM (f (map var vs) . unalias) (compileStrict [] e [])

\end{verbatim}
The code for foreign functions using the \texttt{primitive} calling
convention simply consists of a tail call to the entry point of the
foreign code. For functions using the \texttt{ccall} calling
convention, all arguments are evaluated to ground terms before calling
the foreign function. The result of the call or, if the C function
does not return a result, the constant \texttt{()} is returned from
the compiled function. For functions with result type \texttt{IO}~$t$,
the compiler generates two functions. The first of these returns an
I/O action and the other function implements the I/O action itself.

The runtime system employs the usual state monad approach in order to
implement I/O actions, but with a minor optimization. The type
\texttt{IO} can be defined as
\begin{verbatim}
  type IO a = World -> (a,World)
\end{verbatim}
where \texttt{World} is a type representing the state of the external
world. As this state is already present implicitly in the runtime
system, we can simply use \texttt{()} for it. Because this
representation is constant, the runtime system actually uses a simpler
reader monad for the type \texttt{IO}.
\begin{verbatim}
  type IO a = () -> a
\end{verbatim}

\begin{verbatim}

> compileForeign :: QualIdent -> CallConv -> String -> Type -> [Cam.Decl]
> compileForeign f cc fExt ty
>   | isIO ty' = let (vs,vs') = splitAt (length tys + 1) (nameSupply "_") in
>                [ioFun f' f'_io vs,extFun f'_io vs vs']
>   | otherwise = let (vs,vs') = splitAt (length tys) (nameSupply "_") in
>                 [extFun f' vs vs']
>   where f' = fun f
>         f'_io = Cam.mangleQualified (Cam.demangle f' ++ "/IO")
>         tys = argTypes ty
>         ty' = resultType ty
>         extFun f vs vs' =
>           Cam.FunctionDecl f vs (foreignCall cc fExt vs tys ty' vs')
>         ioFun f f_io (v:vs) =
>           Cam.FunctionDecl f vs
>             (Cam.Seq (bindVar v (Cam.Closure f_io vs)) (Cam.Return v))
>         isIO (TypeConstructor tc tys) = tc == qIOId && length tys == 1
>         isIO _ = False
>         argTypes (TypeArrow ty1 ty2) = ty1 : argTypes ty2
>         argTypes _ = []
>         resultType (TypeArrow _ ty) = resultType ty
>         resultType ty = ty

> foreignCall :: CallConv -> String -> [Cam.Name] -> [Type] -> Type
>             -> [Cam.Name] -> Cam.Stmt
> foreignCall Primitive f vs _ _ _ = Cam.Exec (Cam.mangle f) vs
> foreignCall CCall f vs tys ty ws =
>   foldr2 rigidArg (foreignCCall v (resultType ty) f tys vs') vs vs'
>   where n = length tys
>         (vs',v:_) = splitAt (length tys) ws
>         resultType (TypeConstructor tc tys)
>           | tc == qIOId && length tys == 1 = head tys
>         resultType ty = ty

> rigidArg :: Cam.Name -> Cam.Name -> Cam.Stmt -> Cam.Stmt
> rigidArg v1 v2 st =
>   Cam.Seq (Cam.Eval v2 (Cam.Enter v1))
>           (Cam.Switch Cam.Rigid v2 [Cam.Case Cam.DefaultCase st])

> foreignCCall :: Cam.Name -> Type -> String -> [Type] -> [Cam.Name] -> Cam.Stmt
> foreignCCall v ty ie tys vs
>   | "static" `isPrefixOf` ie =
>       case words (drop 6 ie) of                    {- 6 == length "static" -}
>         [f] -> callStmt Nothing (Cam.StaticCall f xs)
>         [h,f]
>           | h /= "&" -> callStmt (Just h) (Cam.StaticCall f xs)
>           | null xs -> callStmt Nothing (Cam.StaticAddr f)
>         [h,"&",x]
>           | null xs -> callStmt (Just h) (Cam.StaticAddr x)
>         _ -> internalError "foreignCCall (static)"
>   | "dynamic" == ie =
>       case xs of
>         (Cam.TypeFunPtr,x'):xs' -> callStmt Nothing (Cam.DynamicCall x' xs')
>         _ -> internalError "foreignCCall (dynamic)"
>   | otherwise = internalError "foreignCCall"
>   where xs = zip (map cArgType tys) vs
>         callStmt h cc =
>           Cam.Seq (Cam.CCall h (cRetType ty) v cc) (Cam.Return v)

> cArgType :: Type -> Cam.CArgType
> cArgType ty =
>   fromMaybe (internalError ("ccall: invalid argument type " ++ show ty))
>             (cRetType ty)

> cRetType :: Type -> Cam.CRetType
> cRetType (TypeConstructor tc [])
>   | tc == qUnitId = Nothing
>   | tc == qBoolId = Just Cam.TypeBool
>   | tc == qCharId = Just Cam.TypeChar
>   | tc == qIntId = Just Cam.TypeInt
>   | tc == qFloatId = Just Cam.TypeFloat
> cRetType (TypeConstructor tc [_])
>   | tc == qPtrId = Just Cam.TypePtr
>   | tc == qFunPtrId = Just Cam.TypeFunPtr
>   | tc == qStablePtrId = Just Cam.TypeStablePtr
> cRetType ty = internalError ("ccall: invalid result type " ++ show ty)

\end{verbatim}
The selector functions, which are introduced by the compiler in order
to avoid a space leak with lazy pattern bindings (see
p.~\pageref{pattern-binding} in Sect.~\ref{sec:simplify}), have to be
treated specially. The first argument of a selector function is the
pattern to be matched and the remaining arguments are references to
the free variables of the pattern excluding the variable that is
returned by the selector. When a selector is evaluated, it updates the
additional arguments with queue-me nodes first so as to prevent
concurrent computations from evaluating the corresponding selectors.
After matching is complete, these queue-me nodes are updated with
pointers to the matched arguments from the pattern.

The compiler uses the convention that the additional arguments use the
same names as the corresponding variables in the pattern. However, in
the abstract machine code these variables have to use different names.
The function \texttt{compileSelector} takes care of this renaming and
inserts the necessary \texttt{Lock} and \texttt{Update} statements. It
makes use of the fact that the body of a selector is a nested case
expression whose innermost expression is the matched variable.
\begin{verbatim}

> compileSelector :: ([Cam.Name] -> Cam.Stmt -> Cam.Decl)
>                 -> [Ident] -> Expression -> CompState Cam.Decl
> compileSelector f (v:vs) e =
>   do
>     vs' <- mapM (const freshName) vs
>     st <- compileSelectorExpr (zip vs vs') e
>     return (f (var v : vs') (foldr lock st vs'))
>   where lock v = Cam.Seq (Cam.Lock v)

> compileSelectorExpr :: [(Ident,Cam.Name)] -> Expression -> CompState Cam.Stmt
> compileSelectorExpr vs (Case ev (Variable v) [Alt t e]) =
>   do
>     v' <- freshName
>     st <- compileSelectorExpr vs e
>     return (Cam.Seq (Cam.Eval v' (Cam.Enter (var v)))
>                     (Cam.Switch (rf ev) v' [caseTag noVar t st]))
>   where noVar = internalError "invalid selector pattern"
> compileSelectorExpr vs (Variable v) =
>   return (foldr update (Cam.Enter (var v)) vs)
>   where update (v,v') = Cam.Seq (Cam.Update v' (var v))
> compileSelectorExpr _ _ = internalError "invalid selector function"

\end{verbatim}
The compilation of expressions is straight forward. The compiler
attempts to avoid redundant evaluations of nodes. To this end, a list
of the names of those variables whose bindings are known to be in head
normal form, is passed as an additional argument to
\texttt{compileStrict}.
\begin{verbatim}

> compileStrict :: [Ident] -> Expression -> [Cam.Name] -> CompState Cam.Stmt
> compileStrict _ (Literal c) vs = returnWhnf (Literal c) vs
> compileStrict hnfs (Variable v) vs
>   | null vs =
>       return ((if v `elem` hnfs then Cam.Return else Cam.Enter) (var v))
>   | otherwise = return (Cam.Exec (apFun (length vs)) (var v:vs))
> compileStrict _ (Function f arity) vs
>   | n < arity = returnWhnf (Function f arity) vs
>   | otherwise = applyStrict (Cam.Exec (fun f) vs') vs''
>   where n = length vs
>         (vs',vs'') = splitAt arity vs
> compileStrict _ (Constructor c arity) vs =
>   returnWhnf (Constructor c arity) vs
> compileStrict hnfs (Apply e1 e2) vs =
>   do
>     v <- freshName
>     sts <- compileLazy v e2 []
>     st <- compileStrict hnfs e1 (v:vs)
>     return (foldr Cam.Seq st sts)
> compileStrict hnfs (Case ev e as) vs =
>   do
>     v <- freshName
>     st <- compileStrict hnfs e []
>     as' <- mapM (flip (compileCase hnfs v) vs) as
>     return (Cam.Seq (Cam.Eval v st) (Cam.Switch (rf ev) v as'))
> compileStrict hnfs (Or e1 e2) vs =
>   do
>     sts <- mapM (flip (compileStrict hnfs) vs) (branches e1 ++ branches e2)
>     return (Cam.Choices sts)
>   where branches (Or e1 e2) = branches e1 ++ branches e2
>         branches e = [e]
> compileStrict hnfs (Exist v e) vs =
>   do
>     st <- compileStrict (v:hnfs) e vs
>     return (Cam.Seq (bindVar (var v) Cam.Free) st)
> compileStrict hnfs (Let bd e2) vs =
>   do
>     sts <- compileBinding bd
>     st <- compileStrict (addHnfs [bd] hnfs) e2 vs
>     return (foldr Cam.Seq st sts)
> compileStrict hnfs (Letrec bds e) vs =
>   do
>     sts <- compileRecBindings bds
>     st <- compileStrict (addHnfs bds hnfs) e vs
>     return (foldr Cam.Seq st sts)

> returnWhnf :: Expression -> [Cam.Name] -> CompState Cam.Stmt
> returnWhnf e vs =
>   do
>     v <- freshName
>     sts <- compileLazy v e vs
>     return (foldr Cam.Seq (Cam.Return v) sts)

> applyStrict :: Cam.Stmt -> [Cam.Name] -> CompState Cam.Stmt
> applyStrict st vs
>   | null vs = return st
>   | otherwise =
>       do
>         v' <- freshName
>         return (Cam.Seq (Cam.Eval v' st)
>                         (Cam.Exec (apFun (length vs)) (v':vs)))

> literal :: Literal -> Cam.Literal
> literal (Char c) = Cam.Char c
> literal (Int i) = Cam.Int i
> literal (Float f) = Cam.Float f

> addHnfs :: [Binding] -> [Ident] -> [Ident]
> addHnfs bds hnfs = [v | Binding v e <- bds, isHnf hnfs e] ++ hnfs

> isHnf :: [Ident] -> Expression -> Bool
> isHnf _ (Literal _) = True
> isHnf hnfs (Variable v) = v `elem` hnfs
> isHnf _ (Function _ n) = n > 0
> isHnf _ (Constructor _ _) = True
> isHnf _ (Apply e1 e2) = isHnfApp e1 [e2]
> isHnf hnfs (Exist v e) = isHnf (v:hnfs) e
> isHnf hnfs (Let bd e) = isHnf (addHnfs [bd] hnfs) e
> isHnf hnfs (Letrec bds e) = isHnf (addHnfs bds hnfs) e
> isHnf _ _ = internalError "isHnf"

> isHnfApp :: Expression -> [Expression] -> Bool
> isHnfApp (Variable  _) _ = False
> isHnfApp (Function _ n) es = n > length es
> isHnfApp (Constructor _ _) _ = True
> isHnfApp (Apply e1 e2) es = isHnfApp e1 (e2:es)
> isHnfApp (Exist _ e) es = isHnfApp e es
> isHnfApp (Let _ e) es = isHnfApp e es
> isHnfApp (Letrec _ e) es = isHnfApp e es
> isHnfApp _ _ = internalError "isHnfApp"

> rf :: Eval -> Cam.RF
> rf Rigid = Cam.Rigid
> rf Flex  = Cam.Flex

> compileCase :: [Ident] -> Cam.Name -> Alt -> [Cam.Name] -> CompState Cam.Case
> compileCase hnfs v (Alt t e) vs =
>   liftM (caseTag v t) (compileStrict hnfs e vs)

> caseTag :: Cam.Name -> ConstrTerm -> Cam.Stmt -> Cam.Case
> caseTag _ (LiteralPattern l) = Cam.Case (Cam.LitCase (literal l))
> caseTag _ (ConstructorPattern c vs) =
>   Cam.Case (Cam.ConstrCase (con c) (map var vs))
> caseTag v (VariablePattern v') =
>   Cam.Case Cam.DefaultCase . Cam.Seq (bindVar (var v') (Cam.Ref v))

\end{verbatim}
When compiling expressions in lazy -- i.e., argument -- positions,
the compiler generates minimal binding groups in order to improve the
efficiency of the compiler. Note that the compiler can only handle
constants, applications, and let bindings in lazy positions. Case and
non-deterministic or expressions have to be lifted into global
functions before compiling into abstract machine code.
\begin{verbatim}

> compileBinding :: Binding -> CompState [Cam.Stmt0]
> compileBinding (Binding v e) = compileLazy (var v) e []

> compileRecBindings :: [Binding] -> CompState [Cam.Stmt0]
> compileRecBindings =
>   liftM (map Cam.Let . scc bound free . binds . concat) . mapM compileBinding
>   where binds sts = concat [bds | Cam.Let bds <- sts]
>         bound (Cam.Bind v _) = [v]
>         free (Cam.Bind _ n) = vars n
>         vars (Cam.Lit _) = []
>         vars (Cam.Constr _ vs) = vs
>         vars (Cam.Closure _ vs) = vs
>         vars (Cam.Lazy _ vs) = vs
>         vars Cam.Free = []
>         vars (Cam.Ref v) = [v]

> compileLazy :: Cam.Name -> Expression -> [Cam.Name] -> CompState [Cam.Stmt0]
> compileLazy u (Literal l) vs
>   | null vs = return [bindVar u (Cam.Lit (literal l))]
>   | otherwise = internalError "compileLazy(Literal): type error"
> compileLazy u (Variable v) vs = return [bindVar u node]
>   where node
>          | null vs = Cam.Ref (var v)
>          | otherwise = Cam.Lazy (apFun (length vs)) (var v:vs)
> compileLazy u (Function f arity) vs
>   | n < arity = return [bindVar u (Cam.Closure (fun f) vs)]
>   | n == arity = return [bindVar u (Cam.Lazy (fun f) vs)]
>   | otherwise =
>       do
>         v <- freshName
>         return [bindVar v (Cam.Closure (fun f) vs'),
>                 bindVar u (Cam.Lazy (apFun (n - arity)) (v:vs''))]
>   where n = length vs
>         (vs',vs'') = splitAt arity vs
> compileLazy u (Constructor c arity) vs = return [bindVar u node]
>   where n = length vs
>         node
>           | n < arity = Cam.Closure (fun c) vs
>           | n == arity = Cam.Constr (con c) vs
>           | otherwise =
>               internalError ("compileLazy(" ++ show c ++ "): type error")
> compileLazy u (Apply e1 e2) vs =
>   do
>     v <- freshName
>     sts <- compileLazy v e2 []
>     sts' <- compileLazy u e1 (v:vs)
>     return (sts ++ sts')
> compileLazy u (Exist v e) vs =
>   do
>     sts <- compileLazy u e vs
>     return (bindVar (var v) Cam.Free : sts)
> compileLazy u (Let bd e) vs =
>   do
>     sts <- compileBinding bd
>     sts' <- compileLazy u e vs
>     return (sts ++ sts')
> compileLazy u (Letrec bds e) vs =
>   do
>     sts <- compileRecBindings bds
>     sts' <- compileLazy u e vs
>     return (sts ++ sts')
> compileLazy _ e _ = internalError ("compileLazy: " ++ show e)

> bindVar :: Cam.Name -> Cam.Expr -> Cam.Stmt0
> bindVar v n = Cam.Let [Cam.Bind v n]

\end{verbatim}
In a postprocessing step, all \texttt{Ref} bindings are removed from
the generated code.
\begin{verbatim}

> type AliasMap = FM Cam.Name Cam.Name
> unalias :: Cam.Stmt -> Cam.Stmt
> unalias = unaliasStmt zeroFM

> unaliasStmt :: AliasMap -> Cam.Stmt -> Cam.Stmt
> unaliasStmt aliases (Cam.Return v) = Cam.Return (unaliasVar aliases v)
> unaliasStmt aliases (Cam.Enter v) = Cam.Enter (unaliasVar aliases v)
> unaliasStmt aliases (Cam.Exec f vs) =
>   Cam.Exec f (map (unaliasVar aliases) vs)
> unaliasStmt aliases (Cam.Seq st1 st2) = f (unaliasStmt aliases' st2)
>   where (aliases',f) = unaliasStmt0 aliases st1
> unaliasStmt aliases (Cam.Switch rf v cases) =
>   Cam.Switch rf (unaliasVar aliases v) (map (unaliasCase aliases) cases)
> unaliasStmt aliases (Cam.Choices alts) =
>   Cam.Choices (map (unaliasStmt aliases) alts)

> unaliasStmt0 :: AliasMap -> Cam.Stmt0 -> (AliasMap,Cam.Stmt -> Cam.Stmt)
> unaliasStmt0 aliases (Cam.Lock v) =
>   (aliases,Cam.Seq (Cam.Lock (unaliasVar aliases v)))
> unaliasStmt0 aliases (Cam.Update v1 v2) =
>   (aliases,
>    Cam.Seq (Cam.Update (unaliasVar aliases v1) (unaliasVar aliases v2)))
> unaliasStmt0 aliases (Cam.Eval v st) =
>   case unaliasStmt aliases st of
>     Cam.Return v' -> (addToFM v v' aliases,id)
>     st'           -> (aliases,Cam.Seq (Cam.Eval v st'))
> unaliasStmt0 aliases (Cam.Let bds) =
>   (aliases',
>    mkLet [Cam.Bind v (unaliasExpr aliases' n) | Cam.Bind v n <- bds''])
>   where (bds',bds'') = partition isAlias bds
>         aliases' = foldr (uncurry addToFM) aliases
>                          [(v,unaliasVar aliases' v')
>                          | Cam.Bind v (Cam.Ref v') <- bds']
>         mkLet bds = if null bds then id else Cam.Seq (Cam.Let bds)
>         isAlias (Cam.Bind _ (Cam.Ref _)) = True
>         isAlias (Cam.Bind _ _) = False

> unaliasExpr :: AliasMap -> Cam.Expr -> Cam.Expr
> unaliasExpr aliases (Cam.Lit c) = Cam.Lit c
> unaliasExpr aliases (Cam.Constr c vs) =
>   Cam.Constr c (map (unaliasVar aliases) vs)
> unaliasExpr aliases (Cam.Closure f vs) =
>   Cam.Closure f (map (unaliasVar aliases) vs)
> unaliasExpr aliases (Cam.Lazy f vs) =
>   Cam.Lazy f (map (unaliasVar aliases) vs)
> unaliasExpr aliases Cam.Free = Cam.Free

> unaliasCase :: AliasMap -> Cam.Case -> Cam.Case
> unaliasCase aliases (Cam.Case t st) = Cam.Case t (unaliasStmt aliases st)

> unaliasVar :: AliasMap -> Cam.Name -> Cam.Name
> unaliasVar aliases v = fromMaybe v (lookupFM v aliases)

\end{verbatim}
Variable, constructor, and function names have to be mangled into the
external representation used by the abstract machine code.
\begin{verbatim}

> var :: Ident -> Cam.Name
> var v = Cam.mangle (show v)

> fun :: QualIdent -> Cam.Name
> fun f = Cam.mangleQualified (show f)

> apFun :: Int -> Cam.Name
> apFun n = Cam.mangle ('@' : if n == 1 then "" else show n)

> con :: QualIdent -> Cam.Name
> con c = Cam.mangleQualified (show c)

> hiddenCon :: Cam.Name
> hiddenCon = Cam.Name "_"

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> hidden :: QualIdent
> hidden = qualify anonId

> nameSupply :: String -> [Cam.Name]
> nameSupply v = [Cam.Name (v ++ show i) | i <- [0..]]

> freshName :: CompState Cam.Name
> freshName = liftM head (updateSt tail)

> internalError :: String -> a
> internalError what = error ("internal error: " ++ what)

\end{verbatim}
