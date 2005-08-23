% -*- LaTeX -*-
% $Id: CPS.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 2003-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPS.lhs}
\section{Continuation Passing Style}\label{sec:cps}
\begin{verbatim}

> module CPS(CPSFunction(..), CPSCont(..), CaseBlock(..),
>            CPSStmt(..), ChoicesList(..),
>            cpsFunction, cpsApply, cpsVars, contVars,
>            fromCaseBlock, caseBlockTag, fresh) where
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

An abstract machine code function can be transformed into more than
one CPS function. In order to avoid name conflicts, the compiler
assigns an integer number to each CPS function in addition to its
name. By convention, the CPS function that corresponds to the entry
point of an abstract machine code function is always assigned the key
\texttt{0}.

A CPS function has no free variables, i.e., its argument list must
name all variables that are used in the body. The assignments within
the body of a CPS function are split into minimal recursive groups, as
this eases the detection of constants in recursive pattern
declarations, e.g., \verb|let { xs=0:ys; ys=1:xs } in |\dots{} The
\texttt{(Maybe String)} argument of a \texttt{CPSFunction} is used for
defining functions which are to be compiled only if a particular
C-preprocessor constant is defined.
\begin{verbatim}

> data CPSFunction =
>   CPSFunction Name Int (Maybe String) [Name] CPSStmt
>   deriving Show
> data CPSStmt =
>     CPSJump CPSCont
>   | CPSReturn Name (Maybe CPSCont)
>   | CPSEnter Name (Maybe CPSCont)
>   | CPSExec Name [Name] (Maybe CPSCont)
>   | CPSApply Name [Name]
>   | CPSUnify Name Name CPSCont
>   | CPSDelay Name CPSCont
>   | CPSYield (Maybe Name) CPSStmt CPSCont
>   | CPSSeq Stmt0 CPSStmt
>   | CPSSwitch Bool Name (Maybe CPSStmt) [CaseBlock]
>   | CPSLocalSwitch Name CPSStmt CaseBlock
>   | CPSChoices ChoicesList
>   deriving Show

> newtype CPSCont = CPSCont CPSFunction
> data CaseBlock = CaseBlock Int Tag [Name] CPSStmt deriving Show
> data ChoicesList = ChoicesList Name Int [CPSCont] deriving Show

> instance Eq CPSFunction where
>   CPSFunction f1 n1 _ _ _ == CPSFunction f2 n2 _ _ _ = f1 == f2 && n1 == n2
> instance Ord CPSFunction where
>   CPSFunction f1 n1 _ _ _ `compare` CPSFunction f2 n2 _ _ _ =
>     case f1 `compare` f2 of
>       EQ -> n1 `compare` n2
>       ne -> ne

> instance Show CPSCont where
>   showsPrec p (CPSCont (CPSFunction f n _ vs _)) = showParen (p > 10) $
>     showString "CPSCont " . shows f . showChar ' ' . shows n .
>     showChar ' ' . showList vs

> cpsFunction :: Name -> [Name] -> Stmt -> [CPSFunction]
> cpsFunction f vs st = linearize (snd (cps f Nothing vs 0 st))

> cpsApply :: Name -> [Name] -> [CPSFunction]
> cpsApply f vs@(v:vs') = [k0,k1]
>   where k0 = CPSFunction f 0 Nothing vs (CPSEnter v (Just (CPSCont k1)))
>         k1 = CPSFunction f 1 Nothing vs
>                (CPSSwitch False v (Just (CPSDelay v (CPSCont k1)))
>                   [CaseBlock 1 DefaultCase vs (CPSApply v vs')])

> cpsVars :: CPSFunction -> [Name]
> cpsVars (CPSFunction _ _ _ vs _) = vs

> caseBlockTag :: CaseBlock -> Tag
> caseBlockTag (CaseBlock _ t _ _) = t

> fromCaseBlock :: Name -> CaseBlock -> CPSFunction
> fromCaseBlock f (CaseBlock n _ vs st) = CPSFunction f n Nothing vs st

\end{verbatim}
The transformation into CPS is implemented by a top-down algorithm.
The abstract machine code statements \texttt{return}, \texttt{enter},
and \texttt{exec} are transformed directly into their CPS equivalents.
In case of an \texttt{eval} statement, a new continuation, whose first
input argument is the bound variable, is generated from the remaining
statements.

The transformation of a \texttt{switch} statement is more complicated
because the compiler has to introduce auxiliary code for matching
unbound variables. Furthermore, a \texttt{CPSSwitch} cannot be inlined
into the cases of another switch and it must not be preceded by other
statements because they would be executed more than once when the
switch is applied to an unbound variable. This is handled in function
\texttt{cpsJumpSwitch} by generating new functions for switch
statements that occur at invalid positions. Depending on context,
either this function or \texttt{cpsSwitch} is passed as an argument to
\texttt{cpsStmt} and used for translating \texttt{switch} statements.

The translation of a \texttt{choices} statement has to ensure that all
alternatives use the same input variables so that the runtime system
does not need to construct separate closures for each of them.

Note that the transformation ensures that the unique key of every CPS
function is greater than that of its predecessor. This is used below
when transforming a CPS graph into a linear sequence of CPS functions.
\begin{verbatim}

> cps :: Name -> Maybe CPSCont -> [Name] -> Int -> Stmt -> (Int,CPSFunction)
> cps f k ws n st =
>   cpsStmt cpsSwitch f k (CPSFunction f n Nothing vs) (n + 1) st
>   where vs = nub (ws ++ freeVars st k)

> cpsCase :: Name -> Maybe CPSCont -> [Name] -> Int -> Case -> (Int,CaseBlock)
> cpsCase f k ws n (Case t st) =
>   cpsStmt cpsJumpSwitch f k (CaseBlock n t ws) (n + 1) st

> cpsStmt :: (Name -> Maybe CPSCont -> (CPSStmt -> a) -> Int -> RF -> Name 
>             -> [Case] -> (Int,a))
>         -> Name -> Maybe CPSCont -> (CPSStmt -> a) -> Int -> Stmt -> (Int,a)
> cpsStmt _ _ k g n (Return v) = (n,g (CPSReturn v k))
> cpsStmt _ _ k g n (Enter v) = (n,g (CPSEnter v k))
> cpsStmt _ _ k g n (Exec f vs) = (n,g (CPSExec f vs k))
> cpsStmt cpsSwitch f k g n (Seq st1 st2) =
>   case st1 of
>     Lock _ -> cpsStmt cpsJumpSwitch f k (g . CPSSeq st1) n st2
>     Update _ _ -> cpsStmt cpsJumpSwitch f k (g . CPSSeq st1) n st2
>     Eval v st1' -> (n'',k')
>       where (n',k') = cpsStmt cpsSwitch f (Just (CPSCont k'')) g n st1'
>             (n'',k'') = cps f k [v] n' st2
>     Let ds -> cpsStmt cpsJumpSwitch f k (g . splitBinds ds) n st2
>       where splitBinds ds st = foldr (CPSSeq . Let) st (scc bound free ds)
>             bound (Bind v _) = [v]
>             free (Bind _ n) = exprVars n
>     CCall _ _ _ _ -> cpsStmt cpsJumpSwitch f k (g . CPSSeq st1) n st2
> cpsStmt cpsSwitch f k g n (Switch rf v cases) = cpsSwitch f k g n rf v cases
> cpsStmt _ f k g n (Choices alts) = (n'',k')
>   where (n',k') = cpsChoose f g vs n Nothing id ks
>         (n'',ks) = mapAccumL (cps f k vs) n' alts
>         vs = nub (freeVars (Choices alts) k)

> cpsJumpSwitch :: Name -> Maybe CPSCont -> (CPSStmt -> a) -> Int
>               -> RF -> Name -> [Case] -> (Int,a)
> cpsJumpSwitch f k g n rf v cases = (n',g (CPSJump (CPSCont k')))
>   where (n',k') =
>           cpsSwitch f k (CPSFunction f n Nothing vs) (n + 1) rf v cases
>         vs = nub (v : freeVars (Switch rf v cases) k)

> cpsSwitch :: Name -> Maybe CPSCont -> (CPSStmt -> CPSFunction) -> Int
>           -> RF -> Name -> [Case] -> (Int,CPSFunction)
> cpsSwitch f k g n rf v cases = (n'',k')
>   where k' = g (CPSSwitch ub v vcase cases')
>         (n',vcase) = cpsVarCase ub f (CPSCont k') ws n rf v ts
>         (n'',cases') = mapAccumL (cpsCase f k ws) n' cases
>         ws = cpsVars k'
>         ts = [t | Case t _ <- cases, t /= DefaultCase]
>         ub = unboxedSwitch ts

> cpsVarCase :: Bool -> Name -> CPSCont -> [Name] -> Int -> RF -> Name -> [Tag]
>            -> (Int,Maybe CPSStmt)
> cpsVarCase _ _ k _ n Rigid v _ = (n,Just (CPSDelay v k))
> cpsVarCase ub f k ws n Flex v ts
>   | null ts = (n,Nothing)
>   | otherwise = (n',Just (CPSLocalSwitch v (CPSDelay v k) k'))
>   where (n',k') = cpsFlexCase ub f k ws n v ts

> cpsFlexCase :: Bool -> Name -> CPSCont -> [Name] -> Int -> Name -> [Tag]
>             -> (Int,CaseBlock)
> cpsFlexCase _ _ k ws n v [t] =
>   cpsFresh k (\n -> CaseBlock n DefaultCase ws) v n t
> cpsFlexCase ub f k ws n v ts = (n'',k')
>   where (n',k') = cpsChoose f (CaseBlock n DefaultCase ws) ws (n + 1)
>                             (Just v) checkVar ks
>         (n'',ks) =
>           mapAccumL (cpsFresh k (\n -> CPSFunction f n Nothing ws) v) n' ts
>         checkVar st = CPSSwitch ub v (Just st)
>                                 [CaseBlock n DefaultCase ws (CPSJump k)]

> cpsFresh :: CPSCont -> (Int -> CPSStmt -> a) -> Name -> Int -> Tag -> (Int,a)
> cpsFresh k g v n t = (n + 1,g n (foldr CPSSeq (CPSUnify v v' k) (fresh v' t)))
>   where v' = Name "_new"

> cpsChoose :: Name -> (CPSStmt -> a) -> [Name] -> Int -> Maybe Name
>           -> (CPSStmt -> CPSStmt) -> [CPSFunction] -> (Int,a)
> cpsChoose f g ws n v h ks = (n + 1,g (CPSYield v st (CPSCont k)))
>   where k = CPSFunction f n (Just "YIELD_NONDET") ws (h st)
>         st = CPSChoices (ChoicesList f (n - 1) (map CPSCont ks))

> unboxedSwitch :: [Tag] -> Bool
> unboxedSwitch [] = True
> unboxedSwitch (LitCase (Int _) : _) = True
> unboxedSwitch (LitCase _ : _) = False
> unboxedSwitch (ConstrCase _ _ : _) = False
> unboxedSwitch (DefaultCase : cases) = unboxedSwitch cases

> contVars :: CPSCont -> [Name]
> contVars (CPSCont k) = cpsVars k

> tagVars :: Tag -> [Name]
> tagVars (LitCase _) = []
> tagVars (ConstrCase _ vs) = vs
> tagVars DefaultCase = []

> exprVars :: Expr -> [Name]
> exprVars (Lit _) = []
> exprVars (Constr _ vs) = vs
> exprVars (Closure _ vs) = vs
> exprVars (Lazy _ vs) = vs
> exprVars Free = []
> exprVars (Ref v) = [v]

> freeVars :: Stmt -> Maybe CPSCont -> [Name]
> freeVars st k = stmtVars st (maybe [] (tail . contVars) k)

> stmtVars :: Stmt -> [Name] -> [Name]
> stmtVars (Return v) vs = v : vs
> stmtVars (Enter v) vs = v : vs
> stmtVars (Exec _ vs) vs' = vs ++ vs'
> stmtVars (Seq st1 st2) vs = stmt0Vars st1 (stmtVars st2 vs)
> stmtVars (Switch _ v cases) vs = v : concatMap (flip caseVars vs) cases
> stmtVars (Choices alts) vs = concatMap (flip stmtVars vs) alts

> stmt0Vars :: Stmt0 -> [Name] -> [Name]
> stmt0Vars (Lock v) vs = v : vs
> stmt0Vars (Update v1 v2) vs = v1 : v2 : vs
> stmt0Vars (Eval v st) vs = stmtVars st (filter (v /=) vs)
> stmt0Vars (Let ds) vs = filter (`notElemSet` bvs) (fvs ++ vs)
>   where bvs = fromListSet [v | Bind v _ <- ds]
>         fvs = concat [exprVars n | Bind _ n <- ds]
> stmt0Vars (CCall _ _ v cc) vs = ccallVars cc ++ filter (v /=) vs

> caseVars :: Case -> [Name] -> [Name]
> caseVars (Case t st) vs =
>   filter (`notElemSet` fromListSet (tagVars t)) (stmtVars st vs)

> ccallVars :: CCall -> [Name]
> ccallVars (StaticCall _ xs) = map snd xs
> ccallVars (DynamicCall v xs) = v : map snd xs
> ccallVars (StaticAddr _) = []

> fresh :: Name -> Tag -> [Stmt0]
> fresh v (LitCase c) = [Let [Bind v (Lit c)]]
> fresh v (ConstrCase c vs) = map freshVar vs ++ [Let [Bind v (Constr c vs)]]
>   where freshVar v = Let [Bind v Free]

\end{verbatim}
After computing the CPS graph, the CPS functions are linearized in
ascending order. The code uses the unique identifier in order to avoid
duplication of shared continuations.
\begin{verbatim}

> linearize :: CPSFunction -> [CPSFunction]
> linearize = linearizeFun minBound

> linearizeFun :: Int -> CPSFunction -> [CPSFunction]
> linearizeFun n0 (CPSFunction f n c vs st)
>   | n > n0 = CPSFunction f n c vs st : linearizeStmt n st
>   | otherwise = []

> linearizeCont :: Int -> CPSCont -> [CPSFunction]
> linearizeCont n (CPSCont f) = linearizeFun n f

> linearizeStmt :: Int -> CPSStmt -> [CPSFunction]
> linearizeStmt n (CPSJump k) = linearizeCont n k
> linearizeStmt n (CPSReturn _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSEnter _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSExec _ _ k) = maybe [] (linearizeCont n) k
> linearizeStmt _ (CPSApply _ _) = []
> linearizeStmt n (CPSUnify _ _ k) = linearizeCont n k
> linearizeStmt n (CPSDelay _ k) = linearizeCont n k
> linearizeStmt n (CPSYield _ st k) =
>   linMerge [linearizeCont n k,linearizeStmt n st]
> linearizeStmt n (CPSSeq _ st) = linearizeStmt n st
> linearizeStmt n (CPSSwitch _ _ vcase cases) =
>   linMerge (maybe [] (linearizeStmt n) vcase :
>             [linearizeStmt n' st | CaseBlock n' _ _ st <- cases])
> linearizeStmt n (CPSLocalSwitch _ st (CaseBlock n' _ _ st')) =
>   linMerge [linearizeStmt n st,linearizeStmt n' st']
> linearizeStmt n (CPSChoices (ChoicesList _ _ ks)) =
>   linMerge (map (linearizeCont n) ks)

> linMerge :: [[CPSFunction]] -> [CPSFunction]
> linMerge kss = merge (sort kss)
>   where merge [] = []
>         merge [ks] = ks
>         merge ([] : kss) = merge kss
>         merge ((k:ks) : kss) = k : merge (ks : filter ((k /=) . head) kss)

\end{verbatim}
