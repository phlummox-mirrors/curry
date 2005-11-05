% -*- LaTeX -*-
% $Id: CPS.lhs 1814 2005-11-05 22:34:48Z wlux $
%
% Copyright (c) 2003-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPS.lhs}
\section{Continuation Passing Style}\label{sec:cps}
\begin{verbatim}

> module CPS(CPSFunction(..), CPSCont(..),
>            CaseBlock(..), CPSTag(..), CPSStmt(..),
>            cpsFunction, cpsApply, cpsVars, contVars) where
> import Cam
> import List
> import Set
> import SCC

\end{verbatim}
In order to implement concurrent threads and encapsulated search in a
portable way, the compiler first transforms every abstract machine
code function into continuation passing style (CPS). Thus, all return
addresses and in particular the addresses where a computation is
resumed after a thread switch and in an encapsulated search,
respectively, correspond to the address of a function in the
transformed code. During the translation, the compiler also adds code
which instantiates unbound variables in flexible switch statements and
implements stability when it is enabled.

Special code is generated for the private functions that implement
partial applications of tuple constructors and for the functions
\texttt{@}$_n$.

An abstract machine code function may be transformed into more than
one CPS function. In order to avoid name conflicts, the compiler
assigns distinct integer keys to all CPS functions generated from an
abstract machine code function. By convention, the CPS function that
corresponds to the entry point of an abstract machine code function is
always assigned key 0.

No free variables can occur in CPS functions, i.e., their argument
lists must name all variables that are used in the bodies.
\begin{verbatim}

> data CPSFunction = CPSFunction Name Int [Name] CPSStmt deriving Show
> data CPSStmt =
>     CPSJump CPSCont
>   | CPSReturn Expr (Maybe CPSCont)
>   | CPSEnter Name (Maybe CPSCont)
>   | CPSExec Name [Name] (Maybe CPSCont)
>   | CPSCCall CRetType CCall (Maybe CPSCont)
>   | CPSApply Name [Name]
>   | CPSUnify Name Expr CPSCont
>   | CPSDelay Name CPSCont
>   | CPSDelayNonLocal Name CPSCont CPSStmt
>   | CPSSeq Stmt0 CPSStmt
>   | CPSSwitch Bool Name [CaseBlock]
>   | CPSChoices (Maybe (Name,CPSCont)) [CPSCont]
>   deriving Show

> newtype CPSCont = CPSCont CPSFunction
> data CaseBlock = CaseBlock CPSTag CPSStmt deriving Show
> data CPSTag =
>     CPSLitCase Literal
>   | CPSConstrCase Name [Name]
>   | CPSFreeCase
>   | CPSDefaultCase
>   deriving Show

> instance Eq CPSFunction where
>   CPSFunction f1 n1 _ _ == CPSFunction f2 n2 _ _ = f1 == f2 && n1 == n2
> instance Ord CPSFunction where
>   CPSFunction f1 n1 _ _ `compare` CPSFunction f2 n2 _ _ =
>     case f1 `compare` f2 of
>       EQ -> n1 `compare` n2
>       ne -> ne

> instance Show CPSCont where
>   showsPrec p (CPSCont (CPSFunction f n vs _)) = showParen (p > 10) $
>     showString "CPSCont " . shows f . showChar ' ' . shows n .
>     showChar ' ' . showList vs

> cpsFunction :: Name -> [Name] -> Stmt -> [CPSFunction]
> cpsFunction f vs st = linearize (snd (cps f Nothing vs 0 st))

> cpsApply :: Name -> [Name] -> [CPSFunction]
> cpsApply f vs@(v:vs') = [k0,k1]
>   where k0 = CPSFunction f 0 vs (CPSEnter v (Just (CPSCont k1)))
>         k1 = CPSFunction f 1 vs
>                (CPSSwitch False v
>                   [CaseBlock CPSFreeCase (CPSDelay v (CPSCont k1)),
>                    CaseBlock CPSDefaultCase (CPSApply v vs')])

> cpsVars :: CPSFunction -> [Name]
> cpsVars (CPSFunction _ _ vs _) = vs

\end{verbatim}
The transformation into CPS code is implemented by a top-down
algorithm. The abstract machine code statements \texttt{return},
\texttt{enter}, \texttt{exec}, and \texttt{ccall} are transformed
directly into their CPS equivalents. Statement sequences $x$
\texttt{<-} \emph{st$_1$}\texttt{;} \emph{st$_2$}, where \emph{st$_1$}
is neither a \texttt{return} nor a \texttt{ccall} statement, are
transformed by creating a new continuation from \emph{st$_2$}, whose
first input argument is $x$.

The transformation of \texttt{switch} statements is more complicated
because the code of the switch is entered again after an unbound
variable has been instantiated. For that reason, no other code should
precede a transformed \texttt{switch} statement. Furthermore, the
unbound variable cases in transformed \texttt{switch} statements must
know the name of the current function. This is handled by passing on a
continuation for the current function in \texttt{cpsStmt} as long as
no code has been generated. When \texttt{cpsStmt} is about to
transform a \texttt{switch} statement and this continuation is still
available, the statement is transformed with \texttt{cpsSwitch}.
Otherwise \texttt{cpsJumpSwitch} is used, which generates a new
function that performs the switch, and the \texttt{switch} statement is
transformed into a jump to that function.

The translation of a \texttt{choices} statement has to ensure that all
alternatives use the same input variables so that the runtime system
does not need to construct separate closures for each of them.

Note that the transformation ensures that the unique key of every CPS
function is greater than that of its predecessor. This is used below
when transforming a CPS graph into a linear sequence of CPS functions.
\begin{verbatim}

> cps :: Name -> Maybe CPSCont -> [Name] -> Int -> Stmt -> (Int,CPSFunction)
> cps f k ws n st = (n',f')
>   where f' = CPSFunction f n (nub (ws ++ freeVars st k)) st'
>         (n',st') = cpsStmt f (Just (CPSCont f')) k (n + 1) st

> cpsCase :: Name -> Maybe CPSCont -> Int -> Case -> (Int,CaseBlock)
> cpsCase f k n (Case t st) = (n',CaseBlock (cpsTag t) st')
>   where (n',st') = cpsStmt f Nothing k n st

> cpsTag :: Tag -> CPSTag
> cpsTag (LitCase l) = CPSLitCase l
> cpsTag (ConstrCase c vs) = CPSConstrCase c vs
> cpsTag DefaultCase = CPSDefaultCase

> cpsStmt :: Name -> Maybe CPSCont -> Maybe CPSCont -> Int -> Stmt
>         -> (Int,CPSStmt)
> cpsStmt _ _ k n (Return e) = (n,CPSReturn e k)
> cpsStmt _ _ k n (Enter v) = (n,CPSEnter v k)
> cpsStmt _ _ k n (Exec f vs) = (n,CPSExec f vs k)
> cpsStmt _ _ k n (CCall _ ty cc) = (n,CPSCCall ty cc k)
> cpsStmt f k0 k n (Seq st1 st2) =
>   case st1 of
>     Lock _ -> (n',CPSSeq st1 st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     Update _ _ -> (n',CPSSeq st1 st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     v :<- Seq st1' st2' -> cpsStmt f k0 k n (Seq st1' (Seq (v :<- st2') st2))
>     v :<- Return e -> (n',CPSSeq st1 st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     v :<- CCall h ty cc -> (n',CPSSeq st1 st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     v :<- st -> (n'',st1')
>       where (n',st1') = cpsStmt f k0 (Just (CPSCont f')) n st
>             (n'',f') = cps f k [v] n' st2
>     Let ds -> (n',foldr (CPSSeq . Let) st2' (scc bound free ds))
>       where (n',st2') = cpsStmt f Nothing k n st2
>             bound (Bind v _) = [v]
>             free (Bind _ n) = exprVars n
> cpsStmt f k0 k n (Switch rf v cases) =
>   maybe (cpsJumpSwitch f) (cpsSwitch f) k0 k n rf v cases
> cpsStmt f _ k n (Choices alts) = (n',CPSChoices Nothing (map CPSCont ks))
>   where (n',ks) = mapAccumL (cps f k vs) n alts
>         vs = nub (freeVars (Choices alts) k)

> cpsJumpSwitch :: Name -> Maybe CPSCont -> Int -> RF -> Name -> [Case]
>               -> (Int,CPSStmt)
> cpsJumpSwitch f k n rf v cases = (n',CPSJump k')
>   where k' = CPSCont (CPSFunction f n vs st')
>         vs = nub (v : freeVars (Switch rf v cases) k)
>         (n',st') = cpsSwitch f k' k (n + 1) rf v cases

> cpsSwitch :: Name -> CPSCont -> Maybe CPSCont -> Int -> RF -> Name -> [Case]
>           -> (Int,CPSStmt)
> cpsSwitch f k0 k n rf v cases = (n'',CPSSwitch ub v (vcase ++ cases'))
>   where (n',vcase) = cpsVarCase ub f k0 n rf v ts
>         (n'',cases') = mapAccumL (cpsCase f k) n' cases
>         ts = [t | Case t _ <- cases, t /= DefaultCase]
>         ub = unboxedSwitch ts

> cpsVarCase :: Bool -> Name -> CPSCont -> Int -> RF -> Name -> [Tag]
>            -> (Int,[CaseBlock])
> cpsVarCase _ _ k n Rigid v _ = (n,[CaseBlock CPSFreeCase (CPSDelay v k)])
> cpsVarCase ub f k n Flex v ts
>   | null ts = (n,[])
>   | otherwise = (n',[CaseBlock CPSFreeCase (CPSDelayNonLocal v k st')])
>   where (n',st') = cpsFlexCase ub f k n v ts

> cpsFlexCase :: Bool -> Name -> CPSCont -> Int -> Name -> [Tag]
>             -> (Int,CPSStmt)
> cpsFlexCase _ _ k n v [t] = (n,cpsFresh k v t)
> cpsFlexCase ub f k n v ts = (n',CPSChoices (Just (v,k)) (map CPSCont ks))
>   where (n',ks) = mapAccumL fresh n ts
>         fresh n t = (n + 1,CPSFunction f n (contVars k) (cpsFresh k v t))

> cpsFresh :: CPSCont -> Name -> Tag -> CPSStmt
> cpsFresh k v (LitCase l) = CPSUnify v (Lit l) k
> cpsFresh k v (ConstrCase c vs) =
>   foldr CPSSeq (CPSUnify v (Constr c vs) k) (map freshVar vs)
>   where freshVar v = Let [Bind v Free]

> unboxedSwitch :: [Tag] -> Bool
> unboxedSwitch [] = True
> unboxedSwitch (LitCase (Int _) : _) = True
> unboxedSwitch (LitCase _ : _) = False
> unboxedSwitch (ConstrCase _ _ : _) = False
> unboxedSwitch (DefaultCase : cases) = unboxedSwitch cases

> contVars :: CPSCont -> [Name]
> contVars (CPSCont k) = cpsVars k

> freeVars :: Stmt -> Maybe CPSCont -> [Name]
> freeVars st k = stmtVars st (maybe [] (tail . contVars) k)

> stmtVars :: Stmt -> [Name] -> [Name]
> stmtVars (Return e) vs = exprVars e ++ vs
> stmtVars (Enter v) vs = v : vs
> stmtVars (Exec _ vs) vs' = vs ++ vs'
> stmtVars (CCall _ _ cc) vs = ccallVars cc ++ vs
> stmtVars (Seq st1 st2) vs = stmt0Vars st1 (stmtVars st2 vs)
> stmtVars (Switch _ v cases) vs = v : concatMap (flip caseVars vs) cases
> stmtVars (Choices alts) vs = concatMap (flip stmtVars vs) alts

> stmt0Vars :: Stmt0 -> [Name] -> [Name]
> stmt0Vars (Lock v) vs = v : vs
> stmt0Vars (Update v1 v2) vs = v1 : v2 : vs
> stmt0Vars (v :<- st) vs = stmtVars st (filter (v /=) vs)
> stmt0Vars (Let ds) vs = filter (`notElemSet` bvs) (fvs ++ vs)
>   where bvs = fromListSet [v | Bind v _ <- ds]
>         fvs = concat [exprVars n | Bind _ n <- ds]

> caseVars :: Case -> [Name] -> [Name]
> caseVars (Case t st) vs =
>   filter (`notElemSet` fromListSet (tagVars t)) (stmtVars st vs)

> ccallVars :: CCall -> [Name]
> ccallVars (StaticCall _ xs) = map snd xs
> ccallVars (DynamicCall v xs) = v : map snd xs
> ccallVars (StaticAddr _) = []

> exprVars :: Expr -> [Name]
> exprVars (Lit _) = []
> exprVars (Constr _ vs) = vs
> exprVars (Papp _ vs) = vs
> exprVars (Closure _ vs) = vs
> exprVars (Lazy _ vs) = vs
> exprVars Free = []
> exprVars (Var v) = [v]

> tagVars :: Tag -> [Name]
> tagVars (LitCase _) = []
> tagVars (ConstrCase _ vs) = vs
> tagVars DefaultCase = []

\end{verbatim}
After computing the CPS graph, the CPS functions are linearized in
ascending order. The code uses the unique identifier in order to avoid
duplication of shared continuations.
\begin{verbatim}

> linearize :: CPSFunction -> [CPSFunction]
> linearize = linearizeFun minBound

> linearizeFun :: Int -> CPSFunction -> [CPSFunction]
> linearizeFun n0 (CPSFunction f n vs st)
>   | n > n0 = CPSFunction f n vs st : linearizeStmt n st
>   | otherwise = []

> linearizeCont :: Int -> CPSCont -> [CPSFunction]
> linearizeCont n (CPSCont f) = linearizeFun n f

> linearizeStmt :: Int -> CPSStmt -> [CPSFunction]
> linearizeStmt n (CPSJump k) = linearizeCont n k
> linearizeStmt n (CPSReturn _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSEnter _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSExec _ _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSCCall _ _ k) = maybe [] (linearizeCont n) k
> linearizeStmt _ (CPSApply _ _) = []
> linearizeStmt n (CPSUnify _ _ k) = linearizeCont n k
> linearizeStmt n (CPSDelay _ k) = linearizeCont n k
> linearizeStmt n (CPSDelayNonLocal _ k st) =
>   linMerge [linearizeCont n k,linearizeStmt n st]
> linearizeStmt n (CPSSeq _ st) = linearizeStmt n st
> linearizeStmt n (CPSSwitch _ _ cases) =
>   linMerge [linearizeStmt n st | CaseBlock _ st <- cases]
> linearizeStmt n (CPSChoices vk ks) =
>   linMerge (map (linearizeCont n) (maybe id ((:) . snd) vk ks))

> linMerge :: [[CPSFunction]] -> [CPSFunction]
> linMerge kss = merge (sort kss)
>   where merge [] = []
>         merge [ks] = ks
>         merge ([] : kss) = merge kss
>         merge ((k:ks) : kss) =
>           k : merge (sort (ks : filter ((k /=) . head) kss))

\end{verbatim}
