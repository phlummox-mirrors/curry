% -*- LaTeX -*-
% $Id: SyntaxCheck.lhs 1775 2005-09-29 09:24:56Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{SyntaxCheck.lhs}
\section{Syntax Checks}
After the type declarations have been checked, the compiler performs a
syntax check on the remaining declarations. This check disambiguates
nullary data constructors and variables, which cannot be done in the
parser because Curry -- in contrast to many other declarative
languages -- lacks a capitalization convention. In addition, this pass
checks for undefined as well as ambiguous variables and constructors.
Finally, all (adjacent) equations of a function are merged into a
single definition.
\begin{verbatim}

> module SyntaxCheck(syntaxCheck,syntaxCheckGoal) where
> import Base
> import NestEnv
> import Char
> import List
> import Maybe
> import Utils

\end{verbatim}
Syntax checking proceeds as follows. First, the compiler extracts
information about all imported values and data constructors from the
imported (type) environments. Next, the data constructors defined in
the current module are entered into this environment. Finally, all
declarations are checked within the resulting environment.
\begin{verbatim}

> syntaxCheck :: ModuleIdent -> ValueEnv -> [TopDecl] -> (FunEnv,[TopDecl])
> syntaxCheck m tyEnv ds =
>   case linear cs of
>     Linear -> (toplevelEnv env',tds ++ map BlockDecl vds')
>     NonLinear (P p c) -> errorAt p (duplicateData c)
>   where (tds,vds) = partition isTypeDecl ds
>         (env',vds') = checkTopDecls m cs env [d | BlockDecl d <- vds]
>         env = foldr (bindConstrs m) (globalEnv (fmap valueKind tyEnv)) tds
>         cs = concatMap constrs tds

> syntaxCheckGoal :: ValueEnv -> Goal -> Goal
> syntaxCheckGoal tyEnv g = checkGoal (globalEnv (fmap valueKind tyEnv)) g

> bindConstrs :: ModuleIdent -> TopDecl -> VarEnv -> VarEnv
> bindConstrs m (DataDecl _ tc _ cs) env = foldr (bindConstr m) env cs
> bindConstrs m (NewtypeDecl _ tc _ nc) env = bindNewConstr m nc env
> bindConstrs _ (TypeDecl _ _ _ _) env = env
> bindConstrs _ (BlockDecl _) env = env

> bindConstr :: ModuleIdent -> ConstrDecl -> VarEnv -> VarEnv
> bindConstr m (ConstrDecl _ _ c tys) =
>   bindGlobal m c (Constr (qualifyWith m c) (length tys))
> bindConstr m (ConOpDecl _ _ _ op _) =
>   bindGlobal m op (Constr (qualifyWith m op) 2)

> bindNewConstr :: ModuleIdent -> NewConstrDecl -> VarEnv -> VarEnv
> bindNewConstr m (NewConstrDecl _ _ c _) =
>   bindGlobal m c (Constr (qualifyWith m c) 1)

> bindFunc :: ModuleIdent -> P Ident -> VarEnv -> VarEnv
> bindFunc m (P _ f) = bindGlobal m f (Var (qualifyWith m f))

> bindVar :: P Ident -> VarEnv -> VarEnv
> bindVar (P _ v) = bindLocal v (Var (qualify v))

\end{verbatim}
When a module is checked, the global declaration group is checked. A
goal is checked similar to the right hand side of an equation. Thus,
all of its declarations are considered as local declarations. The
final environment can be discarded.
\begin{verbatim}

> checkTopDecls :: ModuleIdent -> [P Ident] -> VarEnv -> [Decl]
>               -> (VarEnv,[Decl])
> checkTopDecls m cs env ds = checkDeclGroup True (bindFunc m) cs env ds

> checkGoal :: VarEnv -> Goal -> Goal
> checkGoal env (Goal p e ds) = env' `seq` Goal p e' ds'
>   where (env',ds') = checkLocalDecls env ds
>         e' = checkExpr p env' e

\end{verbatim}
In each a declaration group, first the left hand sides of all
declarations are checked and adjacent equations for the same function
are merged into a single definition. Next, the compiler checks that
there is a corresponding value definition for every type signature,
evaluation annotation, and infix operator declaration in this group
and that there are no duplicate definitions. Finally, the right hand
sides are checked.

The function \texttt{checkDeclLhs} also handles the case where a
pattern declaration is recognized as a function declaration by the
parser. This happens, e.g., for the declaration \verb|Just x = y|
because the parser cannot distinguish nullary constructors and
functions. Note that pattern declarations are not allowed on the
top-level.
\begin{verbatim}

> checkLocalDecls :: VarEnv -> [Decl] -> (VarEnv,[Decl])
> checkLocalDecls env ds = checkDeclGroup False bindVar [] (nestEnv env) ds

> checkDeclGroup :: Bool -> (P Ident -> VarEnv -> VarEnv) -> [P Ident]
>                -> VarEnv -> [Decl] -> (VarEnv,[Decl])
> checkDeclGroup top bindVar cs env ds = (env',map (checkDeclRhs env') ds')
>   where ds' = joinEquations (map (checkDeclLhs top env) ds)
>         env' = checkDeclVars bindVar cs env ds'

> checkDeclLhs :: Bool -> VarEnv -> Decl -> Decl
> checkDeclLhs _ _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
> checkDeclLhs _ env (TypeSig p vs ty) =
>   TypeSig p (checkVars "type signature" p env vs) ty
> checkDeclLhs _ env (EvalAnnot p fs ev) =
>   EvalAnnot p (checkVars "evaluation annotation" p env fs) ev
> checkDeclLhs top env (FunctionDecl p _ eqs) = checkEquationLhs top env p eqs
> checkDeclLhs _ env (ForeignDecl p cc ie f ty) =
>   ForeignDecl p cc ie (head (checkVars "foreign declaration" p env [f])) ty
> checkDeclLhs top env (PatternDecl p t rhs)
>   | top = internalError "checkDeclLhs"
>   | otherwise = PatternDecl p t' rhs
>   where t' = checkConstrTerm p env t
> checkDeclLhs top env (FreeDecl p vs)
>   | top = internalError "checkDeclLhs"
>   | otherwise = FreeDecl p (checkVars "free variables declaration" p env vs)

> checkEquationLhs :: Bool -> VarEnv -> Position -> [Equation] -> Decl
> checkEquationLhs top env p [Equation p' lhs rhs] =
>   either funDecl (checkDeclLhs top env . patDecl) (checkEqLhs env p' lhs)
>   where funDecl (f,lhs) = FunctionDecl p f [Equation p' lhs rhs]
>         patDecl t
>           | top = errorAt p noToplevelPattern
>           | otherwise = PatternDecl p' t rhs
> checkEquationLhs _ _ _ _ = internalError "checkEquationLhs"

> checkEqLhs :: VarEnv -> Position -> Lhs -> Either (Ident,Lhs) ConstrTerm
> checkEqLhs env _ (FunLhs f ts)
>   | isDataConstr env f = Right (ConstructorPattern (qualify f) ts)
>   | otherwise = Left (f,FunLhs f ts)
> checkEqLhs env _ (OpLhs t1 op t2)
>   | isDataConstr env op = checkOpLhs env (infixPattern t1 (qualify op)) t2
>   | otherwise = Left (op,OpLhs t1 op t2)
>   where infixPattern (InfixPattern t1 op1 t2) op2 t3 =
>           InfixPattern t1 op1 (infixPattern t2 op2 t3)
>         infixPattern t1 op t2 = InfixPattern t1 op t2
> checkEqLhs env p (ApLhs lhs ts) =
>   case checkEqLhs env p lhs of
>     Left (f',lhs') -> Left (f',ApLhs lhs' ts)
>     Right _ -> errorAt p $ nonVariable "curried definition" f
>   where (f,_) = flatLhs lhs

> checkOpLhs :: VarEnv -> (ConstrTerm -> ConstrTerm) -> ConstrTerm
>            -> Either (Ident,Lhs) ConstrTerm
> checkOpLhs env f (InfixPattern t1 op t2)
>   | isJust m || isDataConstr env op' =
>       checkOpLhs env (f . InfixPattern t1 op) t2
>   | otherwise = Left (op',OpLhs (f t1) op' t2)
>   where (m,op') = splitQualIdent op
> checkOpLhs _ f t = Right (f t)

> checkVars :: String -> Position -> VarEnv -> [Ident] -> [Ident]
> checkVars what p env vs =
>   case filter (isDataConstr env) vs of
>     [] -> vs
>     v:_ -> errorAt p (nonVariable what v)

> checkDeclVars :: (P Ident -> VarEnv -> VarEnv) -> [P Ident] -> VarEnv
>               -> [Decl] -> VarEnv
> checkDeclVars bindVar cs env ds =
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
>                     [] -> foldr bindVar env bvs
>                     P p v : _ -> errorAt p (noBody v)
>                 NonLinear (P p v) -> errorAt p (duplicateEvalAnnot v)
>             NonLinear (P p v) -> errorAt p (duplicateTypeSig v)
>         NonLinear (P p v) -> errorAt p (duplicateDefinition v)
>     NonLinear (P p op) -> errorAt p (duplicatePrecedence op)
>   where bvs = concatMap vars (filter isValueDecl ds)
>         tys = concatMap vars (filter isTypeSig ds)
>         evs = concatMap vars (filter isEvalAnnot ds)
>         ops = concatMap vars (filter isInfixDecl ds)

> checkDeclRhs :: VarEnv -> Decl -> Decl
> checkDeclRhs env (FunctionDecl p f eqs) =
>   FunctionDecl p f (map (checkEquation env) eqs)
> checkDeclRhs env (PatternDecl p t rhs) =
>   PatternDecl p t (checkRhs env rhs)
> checkDeclRhs _ (ForeignDecl p cc ie f ty) =
>   ForeignDecl p cc (checkForeign p f cc ie) f ty
> checkDeclRhs _ d = d

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

> checkEquation :: VarEnv -> Equation -> Equation
> checkEquation env (Equation p lhs rhs) = env' `seq` Equation p lhs' rhs'
>   where (env',lhs') = checkLhs p env lhs
>         rhs' = checkRhs env' rhs

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

> checkLhs :: Position -> VarEnv -> Lhs -> (VarEnv,Lhs)
> checkLhs p env lhs = (checkBoundVars p env lhs',lhs')
>   where lhs' = checkLhsTerm p env lhs

> checkLhsTerm :: Position -> VarEnv -> Lhs -> Lhs
> checkLhsTerm p env (FunLhs f ts) = FunLhs f (map (checkConstrTerm p env) ts)
> checkLhsTerm p env (OpLhs t1 op t2) =
>   OpLhs (checkConstrTerm p env t1) op (checkConstrTerm p env t2)
> checkLhsTerm p env (ApLhs lhs ts) =
>   ApLhs (checkLhsTerm p env lhs) (map (checkConstrTerm p env) ts)

> checkArg :: Position -> VarEnv -> ConstrTerm -> (VarEnv,ConstrTerm)
> checkArg p env t = (checkBoundVars p env t',t')
>   where t' = checkConstrTerm p env t

> checkArgs :: Position -> VarEnv -> [ConstrTerm] -> (VarEnv,[ConstrTerm])
> checkArgs p env ts = (checkBoundVars p env ts',ts')
>   where ts' = map (checkConstrTerm p env) ts

> checkBoundVars :: QuantExpr t => Position -> VarEnv -> t -> VarEnv
> checkBoundVars p env ts =
>   case linear bvs of
>     Linear -> foldr (bindVar . P p) (nestEnv env) bvs
>     NonLinear v -> errorAt p (duplicateVariable v)
>   where bvs = bv ts

> checkConstrTerm :: Position -> VarEnv -> ConstrTerm -> ConstrTerm
> checkConstrTerm _ _ (LiteralPattern l) = LiteralPattern l
> checkConstrTerm _ _ (NegativePattern op l) = NegativePattern op l
> checkConstrTerm p env (VariablePattern v)
>   | v == anonId = VariablePattern v
>   | otherwise = checkConstrTerm p env (ConstructorPattern (qualify v) [])
> checkConstrTerm p env (ConstructorPattern c ts) =
>   case qualLookupVar c env of
>     [Constr _ n]
>       | n == n' -> ConstructorPattern c (map (checkConstrTerm p env) ts)
>       | otherwise -> errorAt p (wrongArity c n n')
>       where n' = length ts
>     rs
>       | any isConstr rs -> errorAt p (ambiguousData c)
>       | not (isQualified c) && null ts -> VariablePattern (unqualify c)
>       | otherwise -> errorAt p (undefinedData c)
> checkConstrTerm p env (InfixPattern t1 op t2) =
>   case qualLookupVar op env of
>     [Constr _ n]
>       | n == 2 -> InfixPattern (checkConstrTerm p env t1) op
>                                (checkConstrTerm p env t2)
>       | otherwise -> errorAt p (wrongArity op n 2)
>     rs
>       | any isConstr rs -> errorAt p (ambiguousData op)
>       | otherwise -> errorAt p (undefinedData op)
> checkConstrTerm p env (ParenPattern t) =
>   ParenPattern (checkConstrTerm p env t)
> checkConstrTerm p env (TuplePattern ts) =
>   TuplePattern (map (checkConstrTerm p env) ts)
> checkConstrTerm p env (ListPattern ts) =
>   ListPattern (map (checkConstrTerm p env) ts)
> checkConstrTerm p env (AsPattern v t) =
>   AsPattern (head (checkVars "@ pattern" p env [v])) (checkConstrTerm p env t)
> checkConstrTerm p env (LazyPattern t) =
>   LazyPattern (checkConstrTerm p env t)

> checkRhs :: VarEnv -> Rhs -> Rhs
> checkRhs env (SimpleRhs p e ds) = env' `seq` SimpleRhs p e' ds'
>   where (env',ds') = checkLocalDecls env ds
>         e' = checkExpr p env' e
> checkRhs env (GuardedRhs es ds) = env' `seq` GuardedRhs es' ds'
>   where (env',ds') = checkLocalDecls env ds
>         es' = map (checkCondExpr env') es

> checkCondExpr :: VarEnv -> CondExpr -> CondExpr
> checkCondExpr env (CondExpr p g e) =
>   CondExpr p (checkExpr p env g) (checkExpr p env e)

> checkExpr :: Position -> VarEnv -> Expression -> Expression
> checkExpr _ _ (Literal l) = Literal l
> checkExpr p env (Variable v) =
>   case qualLookupVar v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _ _] -> Constructor v
>     [Var _] -> Variable v
>     rs -> errorAt p (ambiguousIdent rs v)
> checkExpr p env (Constructor c) = checkExpr p env (Variable c)
> checkExpr p env (Paren e) = Paren (checkExpr p env e)
> checkExpr p env (Typed e ty) = Typed (checkExpr p env e) ty
> checkExpr p env (Tuple es) = Tuple (map (checkExpr p env) es)
> checkExpr p env (List es) = List (map (checkExpr p env) es)
> checkExpr p env (ListCompr e qs) = env' `seq` ListCompr e' qs'
>   where (env',qs') = mapAccumL (checkStatement p) env qs
>         e' = checkExpr p env' e
> checkExpr p env (EnumFrom e) = EnumFrom (checkExpr p env e)
> checkExpr p env (EnumFromThen e1 e2) =
>   EnumFromThen (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (EnumFromTo e1 e2) =
>   EnumFromTo (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (EnumFromThenTo e1 e2 e3) =
>   EnumFromThenTo (checkExpr p env e1)
>                  (checkExpr p env e2)
>                  (checkExpr p env e3)
> checkExpr p env (UnaryMinus op e) = UnaryMinus op (checkExpr p env e)
> checkExpr p env (Apply e1 e2) =
>   Apply (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (InfixApply e1 op e2) =
>   InfixApply (checkExpr p env e1) (checkOp p env op) (checkExpr p env e2)
> checkExpr p env (LeftSection e op) =
>   LeftSection (checkExpr p env e) (checkOp p env op)
> checkExpr p env (RightSection op e) =
>   RightSection (checkOp p env op) (checkExpr p env e)
> checkExpr p env (Lambda ts e) = env' `seq` Lambda ts' e'
>   where (env',ts') = checkArgs p env ts
>         e' = checkExpr p env' e
> checkExpr p env (Let ds e) = env' `seq` Let ds' e'
>   where (env',ds') = checkLocalDecls env ds
>         e' = checkExpr p env' e
> checkExpr p env (Do sts e) = env' `seq` Do sts' e'
>   where (env',sts') = mapAccumL (checkStatement p) env sts
>         e' = checkExpr p env' e
> checkExpr p env (IfThenElse e1 e2 e3) =
>   IfThenElse (checkExpr p env e1) (checkExpr p env e2) (checkExpr p env e3)
> checkExpr p env (Case e alts) =
>   Case (checkExpr p env e) (map (checkAlt env) alts)

> checkStatement :: Position -> VarEnv -> Statement -> (VarEnv,Statement)
> checkStatement p env (StmtExpr e) = (env,StmtExpr (checkExpr p env e))
> checkStatement p env (StmtBind t e) =
>   env' `seq` (env',StmtBind t' (checkExpr p env e))
>   where (env',t') = checkArg p env t
> checkStatement p env (StmtDecl ds) = env' `seq` (env',StmtDecl ds')
>   where (env',ds') = checkLocalDecls env ds

> checkAlt :: VarEnv -> Alt -> Alt
> checkAlt env (Alt p t rhs) = env' `seq` Alt p t' rhs'
>   where (env',t') = checkArg p env t
>         rhs' = checkRhs env' rhs

> checkOp :: Position -> VarEnv -> InfixOp -> InfixOp
> checkOp p env op =
>   case qualLookupVar v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _ _] -> InfixConstr v
>     [Var _] -> InfixOp v
>     rs -> errorAt p (ambiguousIdent rs v)
>   where v = opName op

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrs :: TopDecl -> [P Ident]
> constrs (DataDecl _ _ _ cs) = map constr cs
>   where constr (ConstrDecl p _ c _) = P p c
>         constr (ConOpDecl p _ _ op _) = P p op
> constrs (NewtypeDecl _ _ _ (NewConstrDecl p _ c _)) = [P p c]
> constrs (TypeDecl _ _ _ _) = []
> constrs (BlockDecl _) = []

> vars :: Decl -> [P Ident]
> vars (InfixDecl p _ _ ops) = map (P p) ops
> vars (TypeSig p fs _) = map (P p) fs
> vars (EvalAnnot p fs _) = map (P p) fs
> vars (FunctionDecl p f _) = [P p f]
> vars (ForeignDecl p _ _ f _) = [P p f]
> vars (PatternDecl p t _) = map (P p) (bv t)
> vars (FreeDecl p vs) = map (P p) vs

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

> isDataConstr :: VarEnv -> Ident -> Bool
> isDataConstr env v = any isConstr (lookupVar v (globalEnv (toplevelEnv env)))

> isConstr :: ValueKind -> Bool
> isConstr (Constr _ _) = True
> isConstr (Var _) = False

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedVariable :: QualIdent -> String
> undefinedVariable v = qualName v ++ " is undefined"

> undefinedData :: QualIdent -> String
> undefinedData c = "Undefined data constructor " ++ qualName c

> ambiguousIdent :: [ValueKind] -> QualIdent -> String
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
