% -*- LaTeX -*-
% $Id: SyntaxCheck.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{SyntaxCheck.lhs}
\section{Syntax Checks}
After the type declarations have been checked, the compiler performs a
syntax check on the remaining declarations. This check disambiguates
nullary data constructors and variables which -- in contrast to
Haskell -- is not possible on purely syntactic criteria. In addition,
this pass checks for undefined as well as ambiguous variables and
constructors. In order to allow lifting of local definitions in
later phases, all local variables are renamed by adding a unique
key.\footnote{Actually, all variables defined in the same scope share
the same key.} Finally, all (adjacent) equations of a function are
merged into a single definition.
\begin{verbatim}

> module SyntaxCheck(syntaxCheck,syntaxCheckGoal) where
> import Base
> import NestEnv
> import Char
> import List
> import Maybe
> import Monad
> import Combined
> import Utils

\end{verbatim}
Syntax checking proceeds as follows. First, the compiler extracts
information about all imported values and data constructors from the
imported (type) environments. Next, the data constructors defined in
the current module are entered into this environment. Finally, all
declarations are checked within the resulting environment. In
addition, all local variables are renamed.
\begin{verbatim}

> syntaxCheck :: ModuleIdent -> ValueEnv -> [Decl] -> [Decl]
> syntaxCheck m tyEnv ds =
>   case linear cs of
>     Linear -> tds ++ run (checkTopDecls m cs env vds)
>     NonLinear (PIdent p c) -> errorAt p (duplicateData c)
>   where (tds,vds) = partition isTypeDecl ds
>         env = foldr (bindConstrs m) (globalEnv (fmap renameInfo tyEnv)) tds
>         cs = concatMap constrs tds

> syntaxCheckGoal :: ValueEnv -> Goal -> Goal
> syntaxCheckGoal tyEnv g =
>   run (checkGoal (globalEnv (fmap renameInfo tyEnv)) g)

\end{verbatim}
A global state transformer is used for generating fresh integer keys
that are used to rename local variables.
\begin{verbatim}

> type RenameState a = StateT Int Id a

> run :: RenameState a -> a
> run m = runSt m (globalKey + 1)

> newId :: RenameState Int
> newId = updateSt (1 +)

\end{verbatim}
\ToDo{Probably the state transformer should use an \texttt{Integer} 
counter.}

A nested environment is used for recording information about the data
constructors and variables in the module. For every data constructor
its arity is saved. This is used for checking that all constructor
applications in patterns are saturated. For local variables the
environment records the new name of the variable after renaming. No
further information is needed for global variables.
\begin{verbatim}

> type RenameEnv = NestEnv RenameInfo
> data RenameInfo = Constr Int | GlobalVar | LocalVar Ident deriving (Eq,Show)

> globalKey :: Int
> globalKey = uniqueId (mkIdent "")

> renameInfo :: ValueInfo -> RenameInfo
> renameInfo (DataConstructor _ (ForAllExist _ _ ty)) = Constr (arrowArity ty)
> renameInfo (NewtypeConstructor _ _) = Constr 1
> renameInfo _ = GlobalVar

> bindConstrs :: ModuleIdent -> Decl -> RenameEnv -> RenameEnv
> bindConstrs m (DataDecl _ tc _ cs) env = foldr (bindConstr m) env cs
> bindConstrs m (NewtypeDecl _ tc _ nc) env = bindNewConstr m nc env
> bindConstrs _ _ env = env

> bindConstr :: ModuleIdent -> ConstrDecl -> RenameEnv -> RenameEnv
> bindConstr m (ConstrDecl _ _ c tys) = bindGlobal m c (Constr (length tys))
> bindConstr m (ConOpDecl _ _ _ op _) = bindGlobal m op (Constr 2)

> bindNewConstr :: ModuleIdent -> NewConstrDecl -> RenameEnv -> RenameEnv
> bindNewConstr m (NewConstrDecl _ _ c _) = bindGlobal m c (Constr 1)

> bindFunc :: ModuleIdent -> PIdent -> RenameEnv -> RenameEnv
> bindFunc m (PIdent _ f) = bindGlobal m f GlobalVar

> bindVar :: PIdent -> RenameEnv -> RenameEnv
> bindVar (PIdent _ v) env
>   | v' == anonId = env
>   | otherwise = bindLocal v' (LocalVar v) env
>   where v' = unRenameIdent v

> bindGlobal :: ModuleIdent -> Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindGlobal m c r = bindNestEnv c r . qualBindNestEnv (qualifyWith m c) r

> bindLocal :: Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindLocal f r = bindNestEnv f r

> lookupVar :: Ident -> RenameEnv -> [RenameInfo]
> lookupVar v env = lookupNestEnv v env ++! lookupTupleConstr v

> qualLookupVar :: QualIdent -> RenameEnv -> [RenameInfo]
> qualLookupVar v env =
>   qualLookupNestEnv v env ++! lookupTupleConstr (unqualify v)

> lookupTupleConstr :: Ident -> [RenameInfo]
> lookupTupleConstr v
>   | isTupleId v = [Constr (tupleArity v)]
>   | otherwise = []

\end{verbatim}
When a module is checked, the global declaration group is checked. The
resulting renaming environment can be discarded. The same is true for
a goal. Note that all declarations in the goal must be considered as
local declarations.
\begin{verbatim}

> checkTopDecls :: ModuleIdent -> [PIdent] -> RenameEnv -> [Decl]
>               -> RenameState [Decl]
> checkTopDecls m cs env ds =
>   liftM snd (checkDeclGroup (bindFunc m) globalKey cs env ds)

> checkGoal :: RenameEnv -> Goal -> RenameState Goal
> checkGoal env (Goal p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Goal p e' ds')

\end{verbatim}
Each declaration group opens a new scope and uses a distinct key for
renaming the variables in this scope. In a declaration group, first
the left hand sides of all declarations are checked and adjacent
equations for the same function are merged into a single definition.
Next, the compiler checks that there is a corresponding value
definition for every type signature, evaluation annotation, and infix
operator declaration in this group and that there are no duplicate
definitions. Finally, the right hand sides are checked.

The function \texttt{checkDeclLhs} also handles the case where a
pattern declaration is recognized as a function declaration by the
parser. This happens, e.g., for the declaration \verb|Just x = y|
because the parser cannot distinguish nullary constructors and
functions. Note that pattern declarations are not allowed on the
top-level.
\begin{verbatim}

> checkLocalDecls :: RenameEnv -> [Decl] -> RenameState (RenameEnv,[Decl])
> checkLocalDecls env ds =
>   newId >>= \k -> checkDeclGroup bindVar k [] (nestEnv env) ds

> checkDeclGroup :: (PIdent -> RenameEnv -> RenameEnv) -> Int -> [PIdent]
>                -> RenameEnv -> [Decl] -> RenameState (RenameEnv,[Decl])
> checkDeclGroup bindVar k cs env ds =
>   mapM (checkDeclLhs k env) ds >>=
>   checkDecls bindVar cs env . joinEquations

> checkDeclLhs :: Int -> RenameEnv -> Decl -> RenameState Decl
> checkDeclLhs k _ (InfixDecl p fix pr ops) =
>   return (InfixDecl p fix pr (map (flip renameIdent k) ops))
> checkDeclLhs k env (TypeSig p vs ty) =
>   return (TypeSig p (map (checkVar "type signature" k p env) vs) ty)
> checkDeclLhs k env (EvalAnnot p fs ev) =
>   return (EvalAnnot p (map (checkVar "evaluation annotation" k p env) fs) ev)
> checkDeclLhs k env (FunctionDecl p _ eqs) = checkEquationLhs k env p eqs
> checkDeclLhs k env (ForeignDecl p cc ie f ty) =
>   return (ForeignDecl p cc ie (checkVar "foreign declaration" k p env f) ty)
> checkDeclLhs k env (PatternDecl p t rhs) =
>   do
>     t' <- checkConstrTerm k p env t
>     return (PatternDecl p t' rhs)
> checkDeclLhs k env (ExtraVariables p vs) =
>   return (ExtraVariables p
>             (map (checkVar "free variables declaration" k p env) vs))
> checkDeclLhs _ _ d = return d

> checkEquationLhs :: Int -> RenameEnv -> Position -> [Equation]
>                  -> RenameState Decl
> checkEquationLhs k env p [Equation p' lhs rhs] =
>   either (return . funDecl) (checkDeclLhs k env . patDecl)
>          (checkEqLhs k env p' lhs)
>   where funDecl (f,lhs) = FunctionDecl p f [Equation p' lhs rhs]
>         patDecl t
>           | k == globalKey = errorAt p noToplevelPattern
>           | otherwise = PatternDecl p' t rhs
> checkEquationLhs _ _ _ _ = internalError "checkEquationLhs"

> checkEqLhs :: Int -> RenameEnv -> Position -> Lhs
>            -> Either (Ident,Lhs) ConstrTerm
> checkEqLhs k env _ (FunLhs f ts)
>   | isDataConstr f env = Right (ConstructorPattern (qualify f) ts)
>   | otherwise = Left (f',FunLhs f' ts)
>   where f' = renameIdent f k
> checkEqLhs k env _ (OpLhs t1 op t2)
>   | isDataConstr op env = checkOpLhs k env (infixPattern t1 (qualify op)) t2
>   | otherwise = Left (op',OpLhs t1 op' t2)
>   where op' = renameIdent op k
>         infixPattern (InfixPattern t1 op1 t2) op2 t3 =
>           InfixPattern t1 op1 (infixPattern t2 op2 t3)
>         infixPattern t1 op t2 = InfixPattern t1 op t2
> checkEqLhs k env p (ApLhs lhs ts) =
>   case checkEqLhs k env p lhs of
>     Left (f',lhs') -> Left (f',ApLhs lhs' ts)
>     Right _ -> errorAt p $ nonVariable "curried definition" f
>   where (f,_) = flatLhs lhs

> checkOpLhs :: Int -> RenameEnv -> (ConstrTerm -> ConstrTerm) -> ConstrTerm
>            -> Either (Ident,Lhs) ConstrTerm
> checkOpLhs k env f (InfixPattern t1 op t2)
>   | isJust m || isDataConstr op' env =
>       checkOpLhs k env (f . InfixPattern t1 op) t2
>   | otherwise = Left (op'',OpLhs (f t1) op'' t2)
>   where (m,op') = splitQualIdent op
>         op'' = renameIdent op' k
> checkOpLhs _ _ f t = Right (f t)

> checkVar :: String -> Int -> Position -> RenameEnv -> Ident -> Ident
> checkVar what k p env v
>   | isDataConstr v env = errorAt p (nonVariable what v)
>   | otherwise = renameIdent v k

> checkDecls :: (PIdent -> RenameEnv -> RenameEnv) -> [PIdent] -> RenameEnv
>            -> [Decl] -> RenameState (RenameEnv,[Decl])
> checkDecls bindVar cs env ds =
>   case linear ops of
>     Linear ->
>       case linear bvs of
>         Linear ->
>           case linear tys of
>             Linear ->
>               case linear evs of
>                 Linear ->
>                   case filter (`notElem` cs ++ bvs) ops ++
>                        filter (`notElem` bvs) (tys ++ evs) of
>                     [] -> liftM ((,) env') (mapM (checkDeclRhs env') ds)
>                     PIdent p v : _ -> errorAt p (noBody v)
>                 NonLinear (PIdent p v) -> errorAt p (duplicateEvalAnnot v)
>             NonLinear (PIdent p v) -> errorAt p (duplicateTypeSig v)
>         NonLinear (PIdent p v) -> errorAt p (duplicateDefinition v)
>     NonLinear (PIdent p op) -> errorAt p (duplicatePrecedence op)
>   where bvs = concatMap vars (filter isValueDecl ds)
>         tys = concatMap vars (filter isTypeSig ds)
>         evs = concatMap vars (filter isEvalAnnot ds)
>         ops = concatMap vars (filter isInfixDecl ds)
>         env' = foldr bindVar env bvs

> checkDeclRhs :: RenameEnv -> Decl -> RenameState Decl
> checkDeclRhs env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (checkEquation env) eqs)
> checkDeclRhs env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (checkRhs env rhs)
> checkDeclRhs _ (ForeignDecl p cc ie f ty) =
>   return (ForeignDecl p cc (checkForeign p f cc ie) f ty)
> checkDeclRhs _ d = return d

> joinEquations :: [Decl] -> [Decl]
> joinEquations [] = []
> joinEquations (FunctionDecl p f eqs : FunctionDecl p' f' [eq] : ds)
>   | f == f' =
>       if arity (head eqs) == arity eq then
>         joinEquations (FunctionDecl p f (eqs ++ [eq]) : ds)
>       else
>         errorAt p' (differentArity f)
>   where arity (Equation _ lhs _) = length $ snd $ flatLhs lhs
> joinEquations (d : ds) = d : joinEquations ds

> checkEquation :: RenameEnv -> Equation -> RenameState Equation
> checkEquation env (Equation p lhs rhs) =
>   do
>     (env',lhs') <- checkLhs p env lhs
>     rhs' <- checkRhs env' rhs
>     return (Equation p lhs' rhs')

\end{verbatim}
The syntax checker examines the optional import specification of
foreign function declarations. For functions using the \texttt{ccall}
calling convention, the syntax from the Haskell 98 foreign function
interface addendum~\cite{Chakravarty03:FFI} is supported, except for
\texttt{wrapper} specifications, which are not recognized because
callbacks into Curry are not yet supported by the runtime system.
\begin{verbatim}

> checkForeign :: Position -> Ident -> CallConv -> Maybe String -> Maybe String
> checkForeign _ _ CallConvPrimitive ie = ie
> checkForeign p f CallConvCCall ie =
>   maybe (checkFunName f Nothing)
>         (Just . unwords . kind . words . join . break ('&' ==))
>         ie
>   where join (cs,[]) = cs
>         join (cs,c':cs') = cs ++ [' ',c',' '] ++ cs'
>         kind [] = ident []
>         kind (x:xs)
>           | x == "static" = x : header xs
>           | x == "dynamic" = x : end x xs
>           | otherwise = header (x:xs)
>         header [] = ident []
>         header (x:xs)
>           | not (".h" `isSuffixOf` x) = addr (x:xs)
>           | all isHeaderChar x = x : addr xs
>           | otherwise = errorAt p (invalidCImpEnt (notCHeader x) ie)
>         addr [] = ident []
>         addr (x:xs)
>           | x == "&" = x : ident xs
>           | otherwise = ident (x:xs)
>         ident [] = checkFunName f []
>         ident (x:xs)
>           | isCIdent x = x : end ("C identifier " ++ x) xs
>           | otherwise = errorAt p (invalidCImpEnt (notCIdent x) ie)
>         end what xs
>           | null xs = []
>           | otherwise = errorAt p (invalidCImpEnt (junkAfter what) ie)
>         checkFunName f x
>           | isCIdent f' = x
>           | otherwise = errorAt p (invalidCImpEnt (notCIdent f') Nothing)
>           where f' = name f
>         isCIdent [] = False
>         isCIdent (c:cs) = isLetter c && all isLetNum cs
>         isLetter c = isAlpha c || c == '_'
>         isLetNum c = isLetter c || isDigit c
>         isHeaderChar c = isLetNum c || c `elem` "!#$%*+./<=>?@\\^|-~"

> checkLhs :: Position -> RenameEnv -> Lhs -> RenameState (RenameEnv,Lhs)
> checkLhs p env lhs =
>   newId >>= \k ->
>   checkLhsTerm k p env lhs >>=
>   return . checkConstrTerms p (nestEnv env)

> checkLhsTerm :: Int -> Position -> RenameEnv -> Lhs -> RenameState Lhs
> checkLhsTerm k p env (FunLhs f ts) =
>   do
>     ts' <- mapM (checkConstrTerm k p env) ts
>     return (FunLhs f ts')
> checkLhsTerm k p env (OpLhs t1 op t2) =
>   do
>     t1' <- checkConstrTerm k p env t1
>     t2' <- checkConstrTerm k p env t2
>     return (OpLhs t1' op t2')
> checkLhsTerm k p env (ApLhs lhs ts) =
>   do
>     lhs' <- checkLhsTerm k p env lhs
>     ts' <- mapM (checkConstrTerm k p env) ts
>     return (ApLhs lhs' ts')

> checkArgs :: Position -> RenameEnv -> [ConstrTerm]
>           -> RenameState (RenameEnv,[ConstrTerm])
> checkArgs p env ts =
>   newId >>= \k ->
>   mapM (checkConstrTerm k p env) ts >>=
>   return . checkConstrTerms p (nestEnv env)

> checkConstrTerms :: QuantExpr t => Position -> RenameEnv -> t
>                  -> (RenameEnv,t)
> checkConstrTerms p env ts =
>   case linear bvs of
>     Linear -> (foldr (bindVar . PIdent p) env bvs,ts)
>     NonLinear v -> errorAt p (duplicateVariable v)
>   where bvs = bv ts

> checkConstrTerm :: Int -> Position -> RenameEnv -> ConstrTerm
>                 -> RenameState ConstrTerm
> checkConstrTerm _ _ _ (LiteralPattern l) =
>   liftM LiteralPattern (renameLiteral l)
> checkConstrTerm _ _ _ (NegativePattern op l) =
>   liftM (NegativePattern op) (renameLiteral l)
> checkConstrTerm k p env (VariablePattern v)
>   | v == anonId = liftM (VariablePattern . renameIdent anonId) newId
>   | otherwise = checkConstrTerm k p env (ConstructorPattern (qualify v) [])
> checkConstrTerm k p env (ConstructorPattern c ts) =
>   case qualLookupVar c env of
>     [Constr n]
>       | n == n' ->
>           liftM (ConstructorPattern c) (mapM (checkConstrTerm k p env) ts)
>       | otherwise -> errorAt p (wrongArity c n n')
>       where n' = length ts
>     rs
>       | any isConstr rs -> errorAt p (ambiguousData c)
>       | not (isQualified c) && null ts ->
>           return (VariablePattern (renameIdent (unqualify c) k))
>       | otherwise -> errorAt p (undefinedData c)
> checkConstrTerm k p env (InfixPattern t1 op t2) =
>   case qualLookupVar op env of
>     [Constr n]
>       | n == 2 ->
>           do
>             t1' <- checkConstrTerm k p env t1
>             t2' <- checkConstrTerm k p env t2
>             return (InfixPattern t1' op t2')
>       | otherwise -> errorAt p (wrongArity op n 2)
>     rs
>       | any isConstr rs -> errorAt p (ambiguousData op)
>       | otherwise -> errorAt p (undefinedData op)
> checkConstrTerm k p env (ParenPattern t) =
>   liftM ParenPattern (checkConstrTerm k p env t)
> checkConstrTerm k p env (TuplePattern ts) =
>   liftM TuplePattern (mapM (checkConstrTerm k p env) ts)
> checkConstrTerm k p env (ListPattern ts) =
>   liftM ListPattern (mapM (checkConstrTerm k p env) ts)
> checkConstrTerm k p env (AsPattern v t) =
>   liftM (AsPattern (checkVar "@ pattern" k p env v))
>         (checkConstrTerm k p env t)
> checkConstrTerm k p env (LazyPattern t) =
>   liftM LazyPattern (checkConstrTerm k p env t)

> checkRhs :: RenameEnv -> Rhs -> RenameState Rhs
> checkRhs env (SimpleRhs p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (SimpleRhs p e' ds')
> checkRhs env (GuardedRhs es ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     es' <- mapM (checkCondExpr env') es
>     return (GuardedRhs es' ds')

> checkCondExpr :: RenameEnv -> CondExpr -> RenameState CondExpr
> checkCondExpr env (CondExpr p g e) =
>   do
>     g' <- checkExpr p env g
>     e' <- checkExpr p env e
>     return (CondExpr p g' e')

> checkExpr :: Position -> RenameEnv -> Expression -> RenameState Expression
> checkExpr _ _ (Literal l) = liftM Literal (renameLiteral l)
> checkExpr p env (Variable v) =
>   case qualLookupVar v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> return (Constructor v)
>     [GlobalVar] -> return (Variable v)
>     [LocalVar v'] -> return (Variable (qualify v'))
>     rs -> errorAt p (ambiguousIdent rs v)
> checkExpr p env (Constructor c) = checkExpr p env (Variable c)
> checkExpr p env (Paren e) = liftM Paren (checkExpr p env e)
> checkExpr p env (Typed e ty) = liftM (flip Typed ty) (checkExpr p env e)
> checkExpr p env (Tuple es) = liftM Tuple (mapM (checkExpr p env) es)
> checkExpr p env (List es) = liftM List (mapM (checkExpr p env) es)
> checkExpr p env (ListCompr e qs) =
>   do
>     (env',qs') <- mapAccumM (checkStatement p) env qs
>     e' <- checkExpr p env' e
>     return (ListCompr e' qs')
> checkExpr p env (EnumFrom e) = liftM EnumFrom (checkExpr p env e)
> checkExpr p env (EnumFromThen e1 e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (EnumFromThen e1' e2')
> checkExpr p env (EnumFromTo e1 e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (EnumFromTo e1' e2')
> checkExpr p env (EnumFromThenTo e1 e2 e3) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     e3' <- checkExpr p env e3
>     return (EnumFromThenTo e1' e2' e3')
> checkExpr p env (UnaryMinus op e) = liftM (UnaryMinus op) (checkExpr p env e)
> checkExpr p env (Apply e1 e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (Apply e1' e2')
> checkExpr p env (InfixApply e1 op e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (InfixApply e1' (checkOp p env op) e2')
> checkExpr p env (LeftSection e op) =
>   liftM (flip LeftSection (checkOp p env op)) (checkExpr p env e)
> checkExpr p env (RightSection op e) =
>   liftM (RightSection (checkOp p env op)) (checkExpr p env e)
> checkExpr p env (Lambda ts e) =
>   do
>     (env',ts') <- checkArgs p env ts
>     e' <- checkExpr p env' e
>     return (Lambda ts' e')
> checkExpr p env (Let ds e) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Let ds' e')
> checkExpr p env (Do sts e) =
>   do
>     (env',sts') <- mapAccumM (checkStatement p) env sts
>     e' <- checkExpr p env' e
>     return (Do sts' e')
> checkExpr p env (IfThenElse e1 e2 e3) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     e3' <- checkExpr p env e3
>     return (IfThenElse e1' e2' e3')
> checkExpr p env (Case e alts) =
>   do
>     e' <- checkExpr p env e
>     alts' <- mapM (checkAlt env) alts
>     return (Case e' alts')

> checkStatement :: Position -> RenameEnv -> Statement
>                -> RenameState (RenameEnv,Statement)
> checkStatement p env (StmtExpr e) =
>   do
>     e' <- checkExpr p env e
>     return (env,StmtExpr e')
> checkStatement p env (StmtBind t e) =
>   do
>     e' <- checkExpr p env e
>     (env',[t']) <- checkArgs p env [t]
>     return (env',StmtBind t' e')
> checkStatement p env (StmtDecl ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     return (env',StmtDecl ds')

> checkAlt :: RenameEnv -> Alt -> RenameState Alt
> checkAlt env (Alt p t rhs) =
>   do
>     (env',[t']) <- checkArgs p env [t]
>     rhs' <- checkRhs env' rhs
>     return (Alt p t' rhs')

> checkOp :: Position -> RenameEnv -> InfixOp -> InfixOp
> checkOp p env op =
>   case qualLookupVar v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> InfixConstr v
>     [GlobalVar] -> InfixOp v
>     [LocalVar v'] -> InfixOp (qualify v')
>     rs -> errorAt p (ambiguousIdent rs v)
>   where v = opName op

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrs :: Decl -> [PIdent]
> constrs (DataDecl _ _ _ cs) = map constr cs
>   where constr (ConstrDecl p _ c _) = PIdent p c
>         constr (ConOpDecl p _ _ op _) = PIdent p op
> constrs (NewtypeDecl _ _ _ (NewConstrDecl p _ c _)) = [PIdent p c]
> constrs _ = []

> vars :: Decl -> [PIdent]
> vars (InfixDecl p _ _ ops) = map (PIdent p) ops
> vars (TypeSig p fs _) = map (PIdent p) fs
> vars (EvalAnnot p fs _) = map (PIdent p) fs
> vars (FunctionDecl p f _) = [PIdent p f]
> vars (ForeignDecl p _ _ f _) = [PIdent p f]
> vars (PatternDecl p t _) = map (PIdent p) (bv t)
> vars (ExtraVariables p vs) = map (PIdent p) vs
> vars _ = []

> renameLiteral :: Literal -> RenameState Literal
> renameLiteral (Int v i) = liftM (flip Int i . renameIdent v) newId
> renameLiteral l = return l

\end{verbatim}
Due to the lack of a capitalization convention in Curry, it is
possible that an identifier may ambiguously refer to a data
constructor and a function provided that both are imported from some
other module. When checking whether an identifier denotes a
constructor there are two options with regard to ambiguous
identifiers:
\begin{enumerate}
\item Handle the identifier as a data constructor if at least one of
  the imported names is a data constructor.
\item Handle the identifier as a data constructor only if all imported
  entities are data constructors.
\end{enumerate}
We have chosen the first option because otherwise a redefinition of a
constructor can become possible by importing a function with the same
name.
\begin{verbatim}

> isDataConstr :: Ident -> RenameEnv -> Bool
> isDataConstr v = any isConstr . lookupVar v . globalEnv . toplevelEnv

> isConstr :: RenameInfo -> Bool
> isConstr (Constr _) = True
> isConstr GlobalVar = False
> isConstr (LocalVar _) = False

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedVariable :: QualIdent -> String
> undefinedVariable v = qualName v ++ " is undefined"

> undefinedData :: QualIdent -> String
> undefinedData c = "Undefined data constructor " ++ qualName c

> ambiguousIdent :: [RenameInfo] -> QualIdent -> String
> ambiguousIdent rs
>   | any isConstr rs = ambiguousData
>   | otherwise = ambiguousVariable

> ambiguousVariable :: QualIdent -> String
> ambiguousVariable v = "Ambiguous variable " ++ qualName v

> ambiguousData :: QualIdent -> String
> ambiguousData c = "Ambiguous data constructor " ++ qualName c

> duplicateDefinition :: Ident -> String
> duplicateDefinition v = "More than one definition for " ++ name v

> duplicateVariable :: Ident -> String
> duplicateVariable v = name v ++ " occurs more than once in pattern"

> duplicateData :: Ident -> String
> duplicateData c = "More than one definition for data constructor " ++ name c

> duplicateTypeSig :: Ident -> String
> duplicateTypeSig v = "More than one type signature for " ++ name v

> duplicateEvalAnnot :: Ident -> String
> duplicateEvalAnnot v = "More than one eval annotation for " ++ name v

> duplicatePrecedence :: Ident -> String
> duplicatePrecedence op = "More than one fixity declaration for " ++ name op

> nonVariable :: String -> Ident -> String
> nonVariable what c =
>   "Data constructor " ++ name c ++ " in left hand side of " ++ what

> noBody :: Ident -> String
> noBody v = "No definition for " ++ name v ++ " in this scope"

> noToplevelPattern :: String
> noToplevelPattern = "Pattern declaration not allowed at top-level"

> differentArity :: Ident -> String
> differentArity f = "Equations for " ++ name f ++ " have different arities"

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity c arity argc =
>   "Data constructor " ++ qualName c ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> noExpressionStatement :: String
> noExpressionStatement =
>   "Last statement in a do expression must be an expression"

> invalidCImpEnt :: String -> Maybe String -> String
> invalidCImpEnt why Nothing =
>   unlines ["Error in ccall import declaration ",why]
> invalidCImpEnt why (Just ie) =
>   unlines ["Error in ccall import entity specification " ++ show ie,why]

> notCHeader :: String -> String
> notCHeader h = h ++ " is not a valid C header file name"

> notCIdent :: String -> String
> notCIdent f = f ++ " is not a valid C identifier"

> junkAfter :: String -> String
> junkAfter what = "Garbage after " ++ what

\end{verbatim}
