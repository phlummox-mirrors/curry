% -*- LaTeX -*-
% $Id: ILTrans.lhs 1779 2005-10-03 14:55:35Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILTrans.lhs}
\section{Translating Curry into the Intermediate Language}
After desugaring and lifting have been performed, the source code is
translated into the intermediate language. Besides translating from
source terms and expressions into intermediate language terms and
expressions this phase in particular has to implement the pattern
matching algorithm for equations and case expressions.

Because of name conflicts between the source and intermediate language
data structures, we can use only a qualified import for the
\texttt{IL} module.
\begin{verbatim}

> module ILTrans(ilTrans,ilTransIntf) where
> import Base
> import qualified IL
> import Env
> import Maybe
> import List
> import Set
> import TypeTrans
> import Utils

\end{verbatim}
\paragraph{Modules}
At the top-level, the compiler has to translate data type, newtype,
function, and foreign declarations. When translating a data type or
newtype declaration, we ignore the types in the declaration and lookup
the types of the constructors in the type environment instead because
these types are already fully expanded, i.e., they do not include any
alias types.
\begin{verbatim}

> ilTrans :: ValueEnv -> EvalEnv -> Module -> IL.Module
> ilTrans tyEnv evEnv (Module m _ _ ds) = IL.Module m (imports m ds') ds'
>   where ds' = concatMap (translTopDecl m tyEnv evEnv) ds

> translTopDecl :: ModuleIdent -> ValueEnv -> EvalEnv -> TopDecl -> [IL.Decl]
> translTopDecl m tyEnv _ (DataDecl _ tc tvs cs) =
>   [translData m tyEnv tc tvs cs]
> translTopDecl m tyEnv _ (NewtypeDecl _ tc tvs nc) =
>   [translNewtype m tyEnv tc tvs nc]
> translTopDecl _ _ _ (TypeDecl _ _ _ _) = []
> translTopDecl m tyEnv evEnv (BlockDecl d) = translDecl m tyEnv evEnv d

> translDecl :: ModuleIdent -> ValueEnv -> EvalEnv -> Decl -> [IL.Decl]
> translDecl m tyEnv evEnv (FunctionDecl _ f eqs) =
>   [translFunction m tyEnv evEnv f eqs]
> translDecl m tyEnv _ (ForeignDecl _ cc ie f _) =
>   [translForeign m tyEnv f cc (fromJust ie)]
> translDecl _ _ _ _ = []

> translData :: ModuleIdent -> ValueEnv -> Ident -> [Ident] -> [ConstrDecl]
>            -> IL.Decl
> translData m tyEnv tc tvs cs =
>   IL.DataDecl (qualifyWith m tc) (length tvs)
>               (map (translConstrDecl m tyEnv) cs)

> translNewtype :: ModuleIdent -> ValueEnv -> Ident -> [Ident] -> NewConstrDecl
>               -> IL.Decl
> translNewtype m tyEnv tc tvs nc =
>   IL.NewtypeDecl (qualifyWith m tc) (length tvs)
>                  (IL.ConstrDecl c' (translType ty))
>   where c' = qualifyWith m (nconstr nc)
>         TypeArrow ty _ = constrType tyEnv c'

> translConstrDecl :: ModuleIdent -> ValueEnv -> ConstrDecl
>                  -> IL.ConstrDecl [IL.Type]
> translConstrDecl m tyEnv d =
>   IL.ConstrDecl c' (map translType (arrowArgs (constrType tyEnv c')))
>   where c' = qualifyWith m (constr d)

> translForeign :: ModuleIdent -> ValueEnv -> Ident -> CallConv -> String
>               -> IL.Decl
> translForeign m tyEnv f cc ie =
>   IL.ForeignDecl f' (callConv cc) ie (translType (varType tyEnv f'))
>   where f' = qualifyWith m f
>         callConv CallConvPrimitive = IL.Primitive
>         callConv CallConvCCall = IL.CCall

\end{verbatim}
\paragraph{Interfaces}
In order to generate code, the compiler also needs to know the tags
and arities of all imported data constructors. For that reason we
compile the data type declarations of all interfaces into the
intermediate language, too. In this case we do not lookup the
types in the environment because the types in the interfaces are
already fully expanded. Note that we do not translate data types
which are imported into the interface from some other module.
\begin{verbatim}

> ilTransIntf :: Interface -> [IL.Decl]
> ilTransIntf (Interface m _ ds) = foldr (translIntfDecl m) [] ds

> translIntfDecl :: ModuleIdent -> IDecl -> [IL.Decl] -> [IL.Decl]
> translIntfDecl m (IDataDecl _ tc tvs cs) ds
>   | not (isQualified tc) = translIntfData m (unqualify tc) tvs cs : ds
> translIntfDecl _ _ ds = ds

> translIntfData :: ModuleIdent -> Ident -> [Ident] -> [Maybe ConstrDecl]
>                -> IL.Decl
> translIntfData m tc tvs cs =
>   IL.DataDecl (qualifyWith m tc) (length tvs)
>               (map (maybe hiddenConstr (translIntfConstrDecl m tvs)) cs)
>   where hiddenConstr = IL.ConstrDecl qAnonId []
>         qAnonId = qualify anonId

> translIntfConstrDecl :: ModuleIdent -> [Ident] -> ConstrDecl
>                      -> IL.ConstrDecl [IL.Type]
> translIntfConstrDecl m tvs (ConstrDecl _ _ c tys) =
>   IL.ConstrDecl (qualifyWith m c) (map translType (toTypes m tvs tys))
> translIntfConstrDecl m tvs (ConOpDecl _ _ ty1 op ty2) =
>   IL.ConstrDecl (qualifyWith m op) (map translType (toTypes m tvs [ty1,ty2]))

\end{verbatim}
\paragraph{Types}
The type representation in the intermediate language is the same as
the internal representation except that it does not support
constrained type variables and skolem types. The former are fixed and
the latter are replaced by fresh type constructors.
\begin{verbatim}

> translType :: Type -> IL.Type
> translType (TypeConstructor tc tys) =
>   IL.TypeConstructor tc (map translType tys)
> translType (TypeVariable tv) = IL.TypeVariable tv
> translType (TypeConstrained tys _) = translType (head tys)
> translType (TypeArrow ty1 ty2) =
>   IL.TypeArrow (translType ty1) (translType ty2)
> translType (TypeSkolem k) =
>   IL.TypeConstructor (qualify (mkIdent ("_" ++ show k))) []

\end{verbatim}
\paragraph{Functions}
Every function in the program is translated into a function of the
intermediate language. The arguments of the function are renamed such
that all variables occurring in the same position (in different
equations) have the same name. This is necessary in order to
facilitate the translation of pattern matching into \texttt{case}
expressions. We use the following simple convention here: The top-level
arguments of the function are named from left to right \texttt{\_1},
\texttt{\_2}, and so on. The names of nested arguments are constructed
by appending \texttt{\_1}, \texttt{\_2}, etc. from left to right to
the name that were assigned to a variable occurring at the position of
the constructor term.

Some special care is needed for the selector functions introduced by
the compiler in place of pattern bindings. In order to generate the
code for updating all pattern variables, the equality of names between
the pattern variables in the first argument of the selector function
and their repeated occurrences in the remaining arguments must be
preserved. This means that the second and following arguments of a
selector function have to be renamed according to the name mapping
computed for its first argument.

If an evaluation annotation is available for a function, it determines
the evaluation mode of the case expression. Otherwise, the function
uses flexible matching.
\begin{verbatim}

> type RenameEnv = Env Ident Ident

> translFunction :: ModuleIdent -> ValueEnv -> EvalEnv
>                -> Ident -> [Equation] -> IL.Decl
> translFunction m tyEnv evEnv f eqs =
>   IL.FunctionDecl f' vs (translType ty)
>                   (match ev vs (map (translEquation tyEnv vs vs'') eqs))
>   where f' = qualifyWith m f
>         ty = varType tyEnv f'
>         ev = maybe IL.Flex evalMode (lookupEval f evEnv)
>         vs = if isSelectorId f then translArgs eqs vs' else vs'
>         (vs',vs'') = splitAt (arrowArity ty) (argNames (mkIdent ""))

> evalMode :: EvalAnnotation -> IL.Eval
> evalMode EvalRigid = IL.Rigid
> evalMode EvalChoice = error "eval choice is not yet supported"

> translArgs :: [Equation] -> [Ident] -> [Ident]
> translArgs [Equation _ (FunLhs _ (t:ts)) _] (v:_) =
>   v : map (translArg (bindRenameEnv v t emptyEnv)) ts
>   where translArg env (VariablePattern v) = fromJust (lookupEnv v env)

> translEquation :: ValueEnv -> [Ident] -> [Ident] -> Equation
>                -> ([NestedTerm],IL.Expression)
> translEquation tyEnv vs vs' (Equation _ (FunLhs _ ts) rhs) =
>   (zipWith translTerm vs ts,
>    translRhs tyEnv vs' (foldr2 bindRenameEnv emptyEnv vs ts) rhs)

> translRhs :: ValueEnv -> [Ident] -> RenameEnv -> Rhs -> IL.Expression
> translRhs tyEnv vs env (SimpleRhs _ e _) = translExpr tyEnv vs env e

\end{verbatim}
\paragraph{Pattern Matching}
The pattern matching code searches for the left-most inductive
argument position in the left hand sides of all rules defining an
equation. An inductive position is a position where all rules have a
constructor rooted term. If such a position is found, a \texttt{case}
expression is generated for the argument at that position. The
matching code is then computed recursively for all of the alternatives
independently. If no inductive position is found, the algorithm looks
for the left-most demanded argument position, i.e., a position where
at least one of the rules has a constructor rooted term. If such a
position is found, an \texttt{or} expression is generated with those
cases that have a variable at the argument position in one branch and
all other rules in the other branch. If there is no demanded position,
the pattern matching is finished and the compiler translates the right
hand sides of the remaining rules, eventually combining them using
\texttt{or} expressions.

Actually, the algorithm below combines the search for inductive and
demanded positions. The function \texttt{match} scans the argument
lists for the left-most demanded position. If this turns out to be
also an inductive position, the function \texttt{matchInductive} is
called in order to generate a \texttt{case} expression. Otherwise, the
function \texttt{optMatch} is called that tries to find an inductive
position in the remaining arguments. If one is found,
\texttt{matchInductive} is called, otherwise the function
\texttt{optMatch} uses the demanded argument position found by
\texttt{match}.
\begin{verbatim}

> data NestedTerm = NestedTerm IL.ConstrTerm [NestedTerm] deriving Show

> pattern (NestedTerm t _) = t
> arguments (NestedTerm _ ts) = ts

> translLiteral :: Literal -> IL.Literal
> translLiteral (Char c) = IL.Char c
> translLiteral (Int _ i) = IL.Int i
> translLiteral (Float f) = IL.Float f
> translLiteral _ = internalError "translLiteral"

> translTerm :: Ident -> ConstrTerm -> NestedTerm
> translTerm _ (LiteralPattern l) =
>   NestedTerm (IL.LiteralPattern (translLiteral l)) []
> translTerm v (VariablePattern _) = NestedTerm (IL.VariablePattern v) []
> translTerm v (ConstructorPattern c ts) =
>   NestedTerm (IL.ConstructorPattern c (take (length ts) vs))
>              (zipWith translTerm vs ts)
>   where vs = argNames v
> translTerm v (AsPattern _ t) = translTerm v t
> translTerm _ _ = internalError "translTerm"

> bindRenameEnv :: Ident -> ConstrTerm -> RenameEnv -> RenameEnv
> bindRenameEnv _ (LiteralPattern _) env = env
> bindRenameEnv v (VariablePattern v') env = bindEnv v' v env
> bindRenameEnv v (ConstructorPattern _ ts) env =
>   foldr2 bindRenameEnv env (argNames v) ts
> bindRenameEnv v (AsPattern v' t) env = bindEnv v' v (bindRenameEnv v t env)
> bindRenameEnv _ _ env = internalError "bindRenameEnv"

> argNames :: Ident -> [Ident]
> argNames v = [mkIdent (prefix ++ show i) | i <- [1..]]
>   where prefix = name v ++ "_"

> type Match = ([NestedTerm],IL.Expression)
> type Match' = ([NestedTerm] -> [NestedTerm],[NestedTerm],IL.Expression)

> isDefaultPattern :: IL.ConstrTerm -> Bool
> isDefaultPattern (IL.VariablePattern _) = True
> isDefaultPattern _ = False

> isDefaultMatch :: (IL.ConstrTerm,a) -> Bool
> isDefaultMatch = isDefaultPattern . fst

> match :: IL.Eval -> [Ident] -> [Match] -> IL.Expression
> match ev [] alts = foldl1 IL.Or (map snd alts)
> match ev (v:vs) alts
>   | null vars = e1
>   | null nonVars = e2
>   | otherwise = optMatch ev (IL.Or e1 e2) (v:) vs (map skipArg alts)
>   where (vars,nonVars) = partition isDefaultMatch (map tagAlt alts)
>         e1 = matchInductive ev id v vs nonVars
>         e2 = match ev vs (map snd vars)
>         tagAlt (t:ts,e) = (pattern t,(arguments t ++ ts,e))
>         skipArg (t:ts,e) = ((t:),ts,e)

> optMatch :: IL.Eval -> IL.Expression -> ([Ident] -> [Ident]) -> [Ident] ->
>     [Match'] -> IL.Expression
> optMatch ev e prefix [] alts = e
> optMatch ev e prefix (v:vs) alts
>   | null vars = matchInductive ev prefix v vs nonVars
>   | otherwise = optMatch ev e (prefix . (v:)) vs (map skipArg alts)
>   where (vars,nonVars) = partition isDefaultMatch (map tagAlt alts)
>         tagAlt (prefix,t:ts,e) = (pattern t,(prefix (arguments t ++ ts),e))
>         skipArg (prefix,t:ts,e) = (prefix . (t:),ts,e)

> matchInductive :: IL.Eval -> ([Ident] -> [Ident]) -> Ident -> [Ident] ->
>     [(IL.ConstrTerm,Match)] -> IL.Expression
> matchInductive ev prefix v vs alts =
>   IL.Case ev (IL.Variable v) (matchAlts ev prefix vs alts)

> matchAlts :: IL.Eval -> ([Ident] -> [Ident]) -> [Ident] ->
>     [(IL.ConstrTerm,Match)] -> [IL.Alt]
> matchAlts ev prefix vs [] = []
> matchAlts ev prefix vs ((t,alt):alts) =
>   IL.Alt t (match ev (prefix (vars t ++ vs)) (alt : map snd same)) :
>   matchAlts ev prefix vs others
>   where (same,others) = partition ((t ==) . fst) alts 
>         vars (IL.ConstructorPattern _ vs) = vs
>         vars _ = []

\end{verbatim}
Matching in a \texttt{case}-expression works a little bit differently.
In this case, the alternatives are matched from the first to the last
alternative and the first matching alternative is chosen. All
remaining alternatives are discarded.

\ToDo{The case matching algorithm should use type information in order
to detect total matches and immediately discard all alternatives which
cannot be reached.}
\begin{verbatim}

> caseMatch :: ([Ident] -> [Ident]) -> [Ident] -> [Match'] -> IL.Expression
> caseMatch prefix [] alts = thd3 (head alts)
> caseMatch prefix (v:vs) alts
>   | isDefaultMatch (head alts') =
>       caseMatch (prefix . (v:)) vs (map skipArg alts)
>   | otherwise =
>       IL.Case IL.Rigid (IL.Variable v) (caseMatchAlts prefix vs alts')
>   where alts' = map tagAlt alts
>         tagAlt (prefix,t:ts,e) = (pattern t,(prefix,arguments t ++ ts,e))
>         skipArg (prefix,t:ts,e) = (prefix . (t:),ts,e)

> caseMatchAlts ::
>     ([Ident] -> [Ident]) -> [Ident] -> [(IL.ConstrTerm,Match')] -> [IL.Alt]
> caseMatchAlts prefix vs alts = map caseAlt (ts ++ ts')
>   where (ts',ts) = partition isDefaultPattern (nub (map fst alts))
>         caseAlt t =
>           IL.Alt t (caseMatch id (prefix (vars t ++ vs))
>                               (matchingCases t alts))
>         matchingCases t =
>           map (joinArgs (vars t)) . filter (matches t . fst)
>         matches t t' = t == t' || isDefaultPattern t'
>         joinArgs vs (IL.VariablePattern _,(prefix,ts,e)) =
>            (id,prefix (map varPattern vs ++ ts),e)
>         joinArgs _ (_,(prefix,ts,e)) = (id,prefix ts,e)
>         varPattern v = NestedTerm (IL.VariablePattern v) []
>         vars (IL.ConstructorPattern _ vs) = vs
>         vars _ = []

\end{verbatim}
\paragraph{Expressions}
Note that the case matching algorithm assumes that the matched
expression is accessible through a variable. The translation of case
expressions therefore introduces a let binding for the scrutinized
expression and immediately throws it away after the matching -- except
if the matching algorithm has decided to use that variable in the
right hand sides of the case expression. This may happen, for
instance, if one of the alternatives contains an \texttt{@}-pattern.

We also replace applications of newtype constructors by their
arguments. This transformation was already performed during
desugaring, but $\eta$-expansion and optimization may introduce
further possibilities for this transformation.
\begin{verbatim}

> translExpr :: ValueEnv -> [Ident] -> RenameEnv -> Expression -> IL.Expression
> translExpr _ _ _ (Literal l) = IL.Literal (translLiteral l)
> translExpr tyEnv _ env (Variable v) =
>   case lookupVar v env of
>     Just v' -> IL.Variable v'
>     Nothing -> IL.Function v (arrowArity (varType tyEnv v))
>   where lookupVar v env
>           | isQualified v = Nothing
>           | otherwise = lookupEnv (unqualify v) env
> translExpr tyEnv _ _ (Constructor c) =
>   IL.Constructor c (arrowArity (constrType tyEnv c))
> translExpr tyEnv vs env (Apply e1 e2) =
>   case e1 of
>     Constructor c | isNewtypeConstr tyEnv c -> translExpr tyEnv vs env e2
>     _ -> IL.Apply (translExpr tyEnv vs env e1) (translExpr tyEnv vs env e2)
> translExpr tyEnv vs env (Let ds e) =
>   case ds of
>     [FreeDecl _ vs] -> foldr IL.Exist e' vs
>     [d] | all (`notElem` bv d) (qfv emptyMIdent d) ->
>       IL.Let (translBinding env' d) e'
>     _ -> IL.Letrec (map (translBinding env') ds) e'
>   where e' = translExpr tyEnv vs env' e
>         env' = foldr2 bindEnv env bvs bvs
>         bvs = bv ds
>         translBinding env (PatternDecl _ (VariablePattern v) rhs) =
>           IL.Binding v (translRhs tyEnv vs env rhs)
> translExpr tyEnv ~(v:vs) env (Case e alts) =
>   case caseMatch id [v] (map (translAlt v) alts) of
>     IL.Case mode (IL.Variable v') alts'
>       | v == v' && v `notElem` fv alts' -> IL.Case mode e' alts'
>     e''
>       | v `elem` fv e'' -> IL.Let (IL.Binding v e') e''
>       | otherwise -> e''
>   where e' = translExpr tyEnv vs env e
>         translAlt v (Alt _ t rhs) =
>           (id,
>            [translTerm v t],
>            translRhs tyEnv vs (bindRenameEnv v t env) rhs)
> translExpr _ _ _ _ = internalError "translExpr"

> instance Expr IL.Expression where
>   fv (IL.Variable v) = [v]
>   fv (IL.Apply e1 e2) = fv e1 ++ fv e2
>   fv (IL.Case _ e alts) = fv e ++ fv alts
>   fv (IL.Or e1 e2) = fv e1 ++ fv e2
>   fv (IL.Exist v e) = filter (/= v) (fv e)
>   fv (IL.Let (IL.Binding v e1) e2) = fv e1 ++ filter (/= v) (fv e2)
>   fv (IL.Letrec bds e) = filter (`notElem` vs) (fv es ++ fv e)
>     where (vs,es) = unzip [(v,e) | IL.Binding v e <- bds]
>   fv _ = []

> instance Expr IL.Alt where
>   fv (IL.Alt (IL.ConstructorPattern _ vs) e) = filter (`notElem` vs) (fv e)
>   fv (IL.Alt (IL.VariablePattern v) e) = filter (v /=) (fv e)
>   fv (IL.Alt _ e) = fv e

\end{verbatim}
\paragraph{Auxiliary Definitions}
The functions \texttt{varType} and \texttt{constrType} return the type
of variables and constructors, respectively. The quantifiers are
stripped from the types.
\begin{verbatim}

> varType :: ValueEnv -> QualIdent -> Type
> varType tyEnv f =
>   case qualLookupValue f tyEnv of
>     [Value _ (ForAll _ ty)] -> ty
>     _ -> internalError ("varType: " ++ show f)

> constrType :: ValueEnv -> QualIdent -> Type
> constrType tyEnv c =
>   case qualLookupValue c tyEnv of
>     [DataConstructor _ (ForAllExist _ _ ty)] -> ty
>     [NewtypeConstructor _ (ForAllExist _ _ ty)] -> ty
>     _ -> internalError ("constrType: " ++ show c)

> isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
> isNewtypeConstr tyEnv c =
>   case qualLookupValue c tyEnv of
>     [DataConstructor _ _] -> False
>     [NewtypeConstructor _ _] -> True
>     _ -> internalError ("isNewtypeConstr: " ++ show c)

\end{verbatim}
The list of import declarations in the intermediate language code is
determined by collecting all module qualifiers used in the current
module.
\begin{verbatim}

> imports :: ModuleIdent -> [IL.Decl] -> [ModuleIdent]
> imports m = toListSet . deleteFromSet m . fromListSet . flip modules []

> class HasModule a where
>   modules :: a -> [ModuleIdent] -> [ModuleIdent]

> instance HasModule a => HasModule [a] where
>   modules = flip (foldr modules)

> instance HasModule IL.Decl where
>   modules (IL.DataDecl _ _ cs) = modules cs
>   modules (IL.NewtypeDecl _ _ nc) = modules nc
>   modules (IL.FunctionDecl _ _ ty e) = modules ty . modules e
>   modules (IL.ForeignDecl _ _ _ ty) = modules ty

> instance HasModule a => HasModule (IL.ConstrDecl a) where
>   modules (IL.ConstrDecl _ tys) = modules tys

> instance HasModule IL.Type where
>   modules (IL.TypeConstructor tc tys) = modules tc . modules tys
>   modules (IL.TypeVariable _) = id
>   modules (IL.TypeArrow ty1 ty2) = modules ty1 . modules ty2

> instance HasModule IL.ConstrTerm where
>   modules (IL.LiteralPattern _) = id
>   modules (IL.ConstructorPattern c _) = modules c
>   modules (IL.VariablePattern _) = id

> instance HasModule IL.Expression where
>   modules (IL.Literal _) = id
>   modules (IL.Variable _) = id
>   modules (IL.Function f _) = modules f
>   modules (IL.Constructor c _) = modules c
>   modules (IL.Apply e1 e2) = modules e1 . modules e2
>   modules (IL.Case _ e as) = modules e . modules as
>   modules (IL.Or e1 e2) = modules e1 . modules e2
>   modules (IL.Exist _ e) = modules e
>   modules (IL.Let b e) = modules b . modules e
>   modules (IL.Letrec bs e) = modules bs . modules e

> instance HasModule IL.Alt where
>   modules (IL.Alt t e) = modules t . modules e

> instance HasModule IL.Binding where
>   modules (IL.Binding _ e) = modules e

> instance HasModule QualIdent where
>   modules x = maybe id (:) $ fst $ splitQualIdent x

\end{verbatim}
