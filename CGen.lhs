% -*- LaTeX -*-
% $Id: CGen.lhs 1810 2005-10-28 08:06:14Z wlux $
%
% Copyright (c) 1998-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CGen.lhs}
\section{Generating C Code}
\begin{verbatim}

> module CGen(genMain,genEntry,genModule,genSplitModule) where
> import Cam
> import CCode
> import CPS
> import CElim
> import Char
> import List
> import Map
> import Maybe
> import Set
> import Utils

\end{verbatim}
\subsection{Start-up Code}
The functions \texttt{genMain} and \texttt{genEntry} generate the
start-up code for a Curry program. The function \texttt{genMain}
defines the main function of the program and also the global variables
that hold the default sizes of the heap, stack, and trail. The main
function initializes the runtime system by calling \verb|curry_init|,
then calls the specified function that executes the Curry program, and
finally calls \verb|curry_terminate|, which eventually prints the
statistics for the run.
\begin{verbatim}

> genMain :: String -> [CTopDecl]
> genMain run = CppInclude "curry.h" : defaultVars ++ mainFunction run

> defaultVars :: [CTopDecl]
> defaultVars =
>   [CVarDef CPublic ty v (CInit (CExpr (defaultValue v))) | (ty,v) <- vars]
>   where vars = [
>             (ulongType, "heapsize"),
>             (uintType,  "stacksize"),
>             (uintType,  "trailsize"),
>             (intType,   "do_trace"),
>             (intType,   "show_stats")
>           ]
>         defaultValue v = "DEFAULT_" ++ map toUpper v

> mainFunction :: String -> [CTopDecl]
> mainFunction run =
>   [CMainDecl run ["argc","argv"],
>    CMainFunc "main" ["argc","argv"]
>      [procCall "curry_init" ["&argc","argv"],
>       CLocalVar intType "rc" (Just (funCall run ["argc","argv"])),
>       procCall "curry_terminate" [],
>       procCall "exit" ["rc"],
>       CReturn (CInt 0)]]

\end{verbatim}
The function \texttt{genEntry} generates the C function that executes
the Curry program. This is done by invoking \verb|curry_exec| for a
monadic goal and \verb|curry_eval| for a non-monadic goal,
respectively. In the latter case, the code also defines the array
holding the names of the goal's free variables.
\begin{verbatim}

> genEntry :: String -> Name -> Maybe [String] -> [CTopDecl]
> genEntry run f fvs =
>   [CMainFunc run ["argc","argv"]
>     (maybe [] (return . fvDecl "fv_names") fvs ++
>      [CReturn (curry_main fvs (infoTable f) "fv_names" ["argc","argv"])])]
>   where fvDecl v vs =
>           CStaticArray (CPointerType (CConstType "char")) v
>                        (map CInit (map CString vs ++ [CNull]))
>         curry_main (Just _) = curry_eval
>         curry_main Nothing = const . curry_exec
>         curry_exec g args = funCall "curry_exec" (g:args)
>         curry_eval g v args = funCall "curry_eval" (g:v:args)

\end{verbatim}
\subsection{Modules}
The C code for a module is divided into code generated for the data
type declarations and code generated for the function definitions of
the module. Code generation is complicated by a few special cases that
need to be handled. In particular, the compiler must provide
definitions for those tuples that are used in the module and for the
functions \texttt{@}$_n$ that implement applications of a higher-order
variable to $n$ arguments.\footnote{Only functions with $n\geq2$ are
generated. Instead of \texttt{@}$_1$, the function \texttt{@}, which
is implemented in the runtime system, is used.} These functions cannot
be predefined because there are no upper limits on the arity of a
tuple or application. Since these functions may be added in each
module, they must be declared as private -- i.e., \verb|static| --
functions.

\ToDo{The runtime system should preallocate tuple descriptors up to a
reasonable size (e.g., 10). Thus the compiler only has to create
private descriptors if a module uses a tuple with a higher arity.}

In addition, the code generator preallocates the nodes for literal
constants globally. In fact, it preallocates all constants, but this
is done independently. Constant constructors are defined together with
their node info and other constants are allocated separately for every
function because there is not much chance for them to be shared.
\begin{verbatim}

> genModule :: [Decl] -> Module -> CFile
> genModule impDs cam =
>   map CppInclude (nub ("curry.h" : [h | CCall (Just h) _ _ _ <- sts0])) ++
>   genTypes impDs ds sts ns ++
>   genFunctions ds fs sts ns
>   where (_,ds,fs) = splitCam cam
>         (sts0,sts) = foldr linStmts ([],[]) (map thd3 fs)
>         ns = nodes sts0 ++ ccallNodes sts0 ++ flexNodes sts

> linStmts :: Stmt -> ([Stmt0],[Stmt]) -> ([Stmt0],[Stmt])
> linStmts st sts = addStmt st (linStmts' st sts)
>   where addStmt st ~(sts0,sts) = (sts0,st:sts)

> linStmts' :: Stmt -> ([Stmt0],[Stmt]) -> ([Stmt0],[Stmt])
> linStmts' (Return _) sts = sts
> linStmts' (Enter _) sts = sts
> linStmts' (Exec _ _) sts = sts
> linStmts' (Seq st1 st2) sts = addStmt st1 $ linStmts0 st1 $ linStmts st2 sts
>   where addStmt st ~(sts0,sts) = (st:sts0,sts)
>         linStmts0 (Eval _ st) sts = linStmts st sts
>         linStmts0 _ sts = sts
> linStmts' (Switch rf x cs) sts = foldr linStmts sts [st | Case _ st <- cs]
> linStmts' (Choices sts) sts' = foldr linStmts sts' sts

> switchTags :: [Stmt] -> [ConstrDecl]
> switchTags sts =
>   [ConstrDecl c (length vs) | Switch _ _ cs <- sts,
>                               Case (ConstrCase c vs) _ <- cs]

> nodes :: [Stmt0] -> [Expr]
> nodes sts0 = [n | Let bds <- sts0, Bind _ n <- bds]

> ccallNodes :: [Stmt0] -> [Expr]
> ccallNodes sts0
>   | TypeBool `elem` [ty | CCall _ (Just ty) _ _ <- sts0] =
>       [Constr prelTrue [],Constr prelFalse []]
>   | otherwise = []

> flexNodes :: [Stmt] -> [Expr]
> flexNodes sts =
>   [n | Switch Flex _ cs <- sts, Case t _ <- cs, Let ds <- fresh undefined t,
>        Bind _ n <- ds]

\end{verbatim}
The function \texttt{genSplitModule} generates separate C files for
each data type -- except abstract types, i.e., data types with an
empty data constructor list -- and function defined in a module. This
is used for building archive files from the standard library.
\begin{verbatim}

> genSplitModule :: [Decl] -> Module -> [CFile]
> genSplitModule impDs cam =
>   [genModule ms' [DataDecl t cs] | DataDecl t cs <- ds', not (null cs)] ++
>   [genModule (impDs ++ ds') [FunctionDecl f vs st] | (f,vs,st) <- fs]
>   where (ms,ds,fs) = splitCam cam
>         ms' = map ImportDecl ms
>         ds' = map (uncurry DataDecl) ds

\end{verbatim}
\subsection{Data Types and Constants}
For every data type, the compiler defines an enumeration that assigns
tag numbers to its data constructors and also defines node info
structures for every data constructor. The \verb|enum| declarations
are not strictly necessary, but simplify the code generator because it
does not need to determine the tag value of a constructor when it is
used. Furthermore, constant constructors and literal constants are
preallocated. Note that character constants are allocated in a table
defined by the runtime system. Integer constants need to be allocated
only if they cannot be represented in $n-1$ bits where $n$ is the bit
size of the target machine. The generated code uses the preprocessor
macro \texttt{is\_large\_int} defined in the runtime system (see
Sect.~\ref{sec:heap}) in order to determine whether allocation is
necessary. Note that this macro will always return true if the system
was configured with the \texttt{--disable-unboxed} configuration
option.
\begin{verbatim}

> genTypes :: [Decl] -> [(Name,[ConstrDecl])] -> [Stmt] -> [Expr] -> [CTopDecl]
> genTypes impDs ds sts ns =
>   -- imported data constructors
>   [tagDecl t cs | DataDecl t cs <- impDs, any (`elem` usedTs) cs] ++
>   [dataDecl c | DataDecl t cs <- impDs, c <- cs, c `elem` usedCs] ++
>   -- (private) tuple constructors
>   [tagDecl c [ConstrDecl c n] | ConstrDecl c n <- nub (usedTts ++ usedTcs)] ++
>   concatMap (dataDef CPrivate) usedTcs ++
>   -- local data declarations
>   [tagDecl t cs | (t,cs) <- ds] ++
>   concat [dataDecl c : dataDef CPublic c | (_,cs) <- ds, c <- cs] ++
>   -- literal constants
>   literals [c | Lit c <- ns]
>   where constrs = [ConstrDecl c (length vs) | Constr c vs <- ns]
>         (usedTts,usedTs) = partition isTupleConstr (nub (switchTags sts))
>         (usedTcs',usedCs) = partition isTupleConstr (nub constrs)
>         usedTcs = nub (usedTcs' ++ usedTfs)
>         usedTfs = [ConstrDecl f (tupleArity f) | Closure f _ <- ns, isTuple f]
>         isTupleConstr (ConstrDecl c _) = isTuple c

> tagDecl :: Name -> [ConstrDecl] -> CTopDecl
> tagDecl _ cs =
>   CEnumDecl [CConst (dataTag c) (Just n)
>             | (ConstrDecl c _,n) <- zip cs [0..], c /= Name "_"]

> dataDecl :: ConstrDecl -> CTopDecl
> dataDecl (ConstrDecl c n)
>   | n == 0 = CExternVarDecl nodeInfoConstPtrType (constNode c)
>   | otherwise = CExternVarDecl nodeInfoType (dataInfo c)

> dataDef :: CVisibility -> ConstrDecl -> [CTopDecl]
> dataDef vb (ConstrDecl c n)
>   | n == 0 =
>       [CVarDef CPrivate nodeInfoType (dataInfo c) nodeinfo,
>        CVarDef vb nodeInfoConstPtrType (constNode c)
>                (CInit (CAddr (CExpr (dataInfo c))))]
>   | otherwise = [CVarDef vb nodeInfoType (dataInfo c) nodeinfo]
>   where nodeinfo = CStruct (map CInit nodeinfo')
>         nodeinfo' =
>           [CExpr (dataTag c),closureNodeSize n,gcPointerTable,CString name,
>            CExpr "eval_whnf",noEntry,CInt 0,notFinalized]
>         name = snd $ splitQualified $ demangle c

> literals :: [Literal] -> [CTopDecl]
> literals cs =
>   map intConstant (nub [i | Int i <- cs]) ++
>   map floatConstant (nub [f | Float f <- cs])

> intConstant :: Int -> CTopDecl
> intConstant i =
>   CppCondDecls (CFunCall "is_large_int" [CInt i])
>     [CVarDef CPrivate (CConstType "struct int_node") (constInt i)
>              (CStruct $ map CInit [CAddr (CExpr "int_info"),CInt i]),
>      CppDefine (constInt i) (constRef (constInt i))]
>     [CppDefine (constInt i) (CFunCall "mk_unboxed" [CInt i])]

> floatConstant :: Double -> CTopDecl
> floatConstant f =
>   CVarDef CPrivate (CConstType "struct float_node") (constFloat f)
>           (CStruct $ map CInit [CAddr (CExpr "float_info"),fval f])
>   where fval f
>           | isNaN f = error "internalError: NaN literal in CGen.floatConstant"
>           | isInfinite f = CExpr (withSign f "1e500")
>           | otherwise = CFloat f
>         withSign f cs = if f < 0 then '-' : cs else cs

> gcPointerTable, notFinalized :: CExpr
> gcPointerTable = CNull
> notFinalized = CNull
> noEntry = CNull
> noName = CNull

\end{verbatim}
\subsection{Functions}
Besides the code for every function, the compiler must also define
function info vectors for them. These info vectors are used for
constructing closure nodes from (partial) function applications and
also for lazy application nodes. In order to avoid defining redundant
functions, no closure info vector is generated for the \texttt{@}$_n$
functions because they are never applied partially. In addition, no
info vectors for lazy applications are defined for the auxiliary
functions that handle partial applications of data constructors.
\begin{verbatim}

> genFunctions :: [(Name,[ConstrDecl])] -> [(Name,[Name],Stmt)]
>              -> [Stmt] -> [Expr] -> [CTopDecl]
> genFunctions ds fs sts ns =
>   -- imported functions
>   map (entryDecl CPublic) (nonLocal call) ++
>   concatMap closDecl (nonLocal clos) ++
>   map lazyDecl (nonLocal lazy) ++
>   -- (private) @ functions
>   [entryDecl CPrivate (apName n) | n <- [3..maxApArity]] ++
>   concat [evalDef CPrivate f n | f <- apClos, let n = apArity f, n > 2] ++
>   concat [lazyDef CPrivate f n | f <- apLazy, let n = apArity f, n > 2] ++
>   concat [apFunction (apName n) n | n <- [3..maxApArity]] ++
>   -- (private) tuple functions (for partial applications)
>   map (entryDecl CPrivate) tupleClos ++
>   concat [closDef CPrivate f (tupleArity f) | f <- tupleClos] ++
>   concatMap tupleFunction tupleClos ++
>   -- local function declarations
>   map (entryDecl CPublic . fst3) fs ++
>   concat [closDecl f ++ closDef CPublic f (length vs) | (f,vs,_) <- fs] ++
>   concat [lazyDecl f : lazyDef CPublic f (length vs) | (f,vs,_) <- fs,
>                                                        f `notElem` cs] ++
>   concat [function CPublic f vs st | (f,vs,st) <- fs]
>   where nonLocal = filter (`notElem` map fst3 fs)
>         (tupleClos,clos) = partition isTuple clos'
>         (apCall,call) = partition isAp (nub [f | Exec f _ <- sts])
>         (apClos,clos') = partition isAp (nub [f | Closure f _ <- ns])
>         (apLazy,lazy) = partition isAp (nub [f | Lazy f _ <- ns])
>         maxApArity = maximum (0 : map apArity (apCall ++ apClos ++ apLazy))
>         cs = [c | ConstrDecl c _ <- concatMap snd ds]

> entryDecl :: CVisibility -> Name -> CTopDecl
> entryDecl vb f = CFuncDecl vb (cName f)

> evalEntryDecl :: Name -> CTopDecl
> evalEntryDecl f = CFuncDecl CPrivate (evalFunc f)

> lazyEntryDecl :: Name -> CTopDecl
> lazyEntryDecl f = CFuncDecl CPrivate (lazyFunc f)

> closDecl :: Name -> [CTopDecl]
> closDecl f =
>   [CExternArrayDecl nodeInfoType (infoTable f),
>    CExternVarDecl (CConstType "struct closure_node") (constFunc f)]

> lazyDecl :: Name -> CTopDecl
> lazyDecl f = CExternArrayDecl nodeInfoType (lazyInfoTable f)

> evalDef :: CVisibility -> Name -> Int -> [CTopDecl]
> evalDef vb f n =
>   [evalEntryDecl f,
>    CVarDef vb nodeInfoType (dataInfo f) (funInfo f n n),
>    evalFunction f n]

> closDef :: CVisibility -> Name -> Int -> [CTopDecl]
> closDef vb f n =
>   [evalEntryDecl f,
>    CArrayDef vb nodeInfoType (infoTable f) [funInfo f i n | i <- [0..n]],
>    CVarDef vb (CConstType "struct closure_node") (constFunc f)
>            (CStruct [CInit (CExpr (infoTable f)),CStruct [CInit CNull]]),
>    evalFunction f n]

> lazyDef :: CVisibility -> Name -> Int -> [CTopDecl]
> lazyDef vb f n =
>   [lazyEntryDecl f,
>    CArrayDef vb nodeInfoType (lazyInfoTable f)
>              (map (CStruct . map CInit) [suspinfo,queuemeinfo,indirinfo]),
>    lazyFunction f n]
>   where suspinfo =
>           [CExpr "SUSPEND_TAG",suspendNodeSize n,gcPointerTable,
>            CString (undecorate (demangle f)),CExpr (lazyFunc f),noEntry,
>            CInt 0,notFinalized]
>         queuemeinfo =
>           [CExpr "QUEUEME_TAG",suspendNodeSize n,gcPointerTable,
>            noName,CExpr "eval_queueMe",noEntry,CInt 0,notFinalized]
>         indirinfo =
>           [CExpr "INDIR_TAG",suspendNodeSize n,gcPointerTable,
>            noName,CExpr "eval_indir",noEntry,CInt 0,notFinalized]

> funInfo :: Name -> Int -> Int -> CInitializer
> funInfo f i n = CStruct (map CInit funinfo)
>   where funinfo =
>           [CExpr (if i < n then "PAPP_TAG" else "FAPP_TAG"),
>            closureNodeSize i,gcPointerTable,CString (undecorate (demangle f)),
>            CExpr (if i < n then "eval_whnf" else evalFunc f),
>            CExpr (cName f),CInt n,notFinalized]

\end{verbatim}
\subsection{Code Generation}
The compiler transforms each abstract machine code function into a
list of continuation passing style functions, and translates all of
these functions into distinct C functions. In addition, the compiler
generates the evaluation code for the fully applied closure node and
the suspend node associated with the abstract machine code function.
\begin{verbatim}

> function :: CVisibility -> Name -> [Name] -> Stmt -> [CTopDecl]
> function vb f vs st = funcDefs vb f vs (cpsFunction f vs st)

> evalFunction :: Name -> Int -> CTopDecl
> evalFunction f n = CFuncDef CPrivate (evalFunc f) (evalCode f n)
>   where evalCode f n =
>           [CProcCall "CHECK_STACK" [CInt (n - 1)] | n > 1] ++
>           CLocalVar nodePtrType "clos" (Just (CExpr "sp[0]")) :
>           [CDecrBy (LVar "sp") (CInt (n - 1)) | n /= 1] ++
>           [saveArg i | i <- [0..n-1]] ++ [goto (cName f)]
>         saveArg i = CAssign (LElem (LVar "sp") (CInt i))
>                             (CElem (CExpr "clos->c.args") (CInt i))

> lazyFunction :: Name -> Int -> CTopDecl
> lazyFunction f n = CFuncDef CPrivate (lazyFunc f) (lazyCode f n)
>   where lazyCode f n =
>           CLocalVar nodePtrType "susp" (Just (CExpr "sp[0]")) :
>           CIf (CFunCall "!is_local_space" [field "susp" "s.spc"])
>               [CProcCall "suspend_search"
>                          [CExpr "resume",CExpr "susp",field "susp" "s.spc"],
>                CAssign (LVar "susp") (CExpr "sp[0]")]
>               [] :
>           CProcCall "CHECK_STACK" [CInt (n + 1)] :
>           CDecrBy (LVar "sp") (CInt (n + 1)) :
>           [saveArg i | i <- [0..n-1]] ++
>           [CAssign (LElem (LVar "sp") (CInt n)) (asNode (CExpr "update"))] ++
>           lock (Name "susp") ++
>           [goto (cName f)]
>         saveArg i = CAssign (LElem (LVar "sp") (CInt i))
>                             (CElem (CExpr "susp->s.args") (CInt i))

> tupleFunction :: Name -> [CTopDecl]
> tupleFunction f = function CPrivate f vs (tuple v vs)
>   where n = tupleArity f
>         (v:vs) = [Name ('v' : show i) | i <- [0..n]]
>         tuple v vs = Seq (Let [Bind v (Constr f vs)]) (Return v)

> apFunction :: Name -> Int -> [CTopDecl]
> apFunction f n = funcDefs CPrivate f vs (cpsApply f vs)
>   where vs = [Name ('v' : show i) | i <- [1..n]]

> funcDefs :: CVisibility -> Name -> [Name] -> [CPSFunction] -> [CTopDecl]
> funcDefs vb f vs (k:ks) =
>   map privFuncDecl ks ++ entryDef vb f vs k : map funcDef ks

> privFuncDecl :: CPSFunction -> CTopDecl
> privFuncDecl k = CFuncDecl CPrivate (cpsName k)

> entryDef :: CVisibility -> Name -> [Name] -> CPSFunction -> CTopDecl
> entryDef vb f vs k
>   | vs == cpsVars k =
>       CFuncDef vb (cpsName k) (entryCode f (length vs) : funCode k)
>   | otherwise = error ("internal error: entryDef " ++ demangle f)

> funcDef :: CPSFunction -> CTopDecl
> funcDef k = CFuncDef CPrivate (cpsName k) (funCode k)

> entryCode :: Name -> Int -> CStmt
> entryCode f n =
>   CTrace "%I enter %s%V\n"
>          [CString (undecorate (demangle f)),CInt n,CExpr "sp"]

\end{verbatim}
The compiler generates a C function from every CPS function. At the
beginning of a function, stack and heap checks are performed if
necessary. After the heap check, the function's arguments are loaded
from the stack. When generating code for the cases in a
\texttt{switch} statement, we try to reuse these variables.
However, if the case code performs a heap check, the variables
have to be reloaded from the stack because the garbage collector does
not trace local variables. Note that the code generated by
\texttt{caseCode} is enclosed in a \texttt{CBlock} so that the
declarations generated by \texttt{loadVars} are not moved to a place
where they might inadvertently shadow the variables loaded at the
beginning of the function.

When saving arguments to the stack, we avoid saving variables that
were loaded from the same offset in the stack because the optimizer of
the Gnu C compiler does not detect such redundant save operations.
\begin{verbatim}

> funCode :: CPSFunction -> [CStmt]
> funCode (CPSFunction _ _ vs st) =
>   elimUnused (stackCheck vs st ++ heapCheck consts ds tys ++ loadVars vs ++
>               constDefs consts ds ++ cCode consts vs st)
>   where ds = concat dss
>         (tys,dss) = allocs st
>         consts = constants dss

> caseCode :: [Name] -> Name -> CPSTag -> CPSStmt -> [CStmt]
> caseCode vs v t st =
>   [CBlock (stackCheck vs st ++ heapCheck' consts ds tys vs ++
>            fetchArgs v t ++ constDefs consts ds ++ cCode consts vs st)]
>   where ds = concat dss
>         (tys,dss) = allocs st
>         consts = constants dss
>         heapCheck' consts ds tys vs
>           | null sts = []
>           | otherwise = sts ++ loadVars vs
>           where sts = heapCheck consts ds tys

> loadVars :: [Name] -> [CStmt]
> loadVars vs = zipWith loadVar vs [0..]
>   where loadVar v i =
>           CLocalVar nodePtrType (show v) (Just (CElem (CExpr "sp") (CInt i)))

> fetchArgs :: Name -> CPSTag -> [CStmt]
> fetchArgs _ (CPSLitCase _) = []
> fetchArgs v (CPSConstrCase _ vs) =
>   assertRel (funCall "closure_argc" [show v]) "==" (CInt (length vs)) :
>   zipWith (fetchArg (field (show v) "c.args")) vs [0..]
>   where fetchArg v v' =
>           CLocalVar nodePtrType (show v') . Just . CElem v . CInt
> fetchArgs _ CPSFreeCase = []
> fetchArgs _ CPSDefaultCase = []

> saveVars :: [Name] -> [Name] -> [CStmt]
> saveVars vs0 vs =
>   [CIncrBy (LVar "sp") (CInt d) | d /= 0] ++
>   [saveVar i v | (i,v0,v) <- zip3 [0..] vs0' vs, v0 /= v]
>   where d = length vs0 - length vs
>         vs0' = if d >= 0 then drop d vs0 else replicate (-d) (Name "") ++ vs0
>         saveVar i v = CAssign (LElem (LVar "sp") (CInt i)) (CExpr (show v))

> updVar :: [Name] -> Name -> CStmt
> updVar vs v
>   | null vs'' = error ("updVar " ++ show v)
>   | otherwise =
>       CAssign (LElem (LVar "sp") (CInt (length vs'))) (CExpr (show v))
>   where (vs',vs'') = break (v ==) vs

\end{verbatim}
When computing the heap requirements of a function, we have to take
into account nodes that are allocated explicitly in \verb|let|
statements and implicitly for the results of \verb|ccall| statements,
but can ignore nodes which are allocated outside of the heap, i.e.,
literal constants and character nodes.
\begin{verbatim}

> heapCheck :: FM Name CExpr -> [Bind] -> [CArgType] -> [CStmt]
> heapCheck consts ds tys = [CProcCall "CHECK_HEAP" [n] | n /= CInt 0]
>   where n = foldr add (CInt 0)
>                   ([ctypeSize ty | ty <- tys] ++
>                    [nodeSize n | Bind v n <- ds, not (isConstant consts v)])
 
> allocs :: CPSStmt -> ([CArgType],[[Bind]])
> allocs (CPSSeq st1 st2) = allocs0 st1 (allocs st2)
>   where allocs0 (Let ds) ~(tys,dss) = (tys,ds:dss)
>         allocs0 (CCall _ (Just ty) _ _) ~(tys,dss) = (ty:tys,dss)
>         allocs0 _ as = as
> allocs (CPSDelayNonLocal _ _ st) = allocs st
> allocs _ = ([],[])

> nodeSize :: Expr -> CExpr
> nodeSize (Lit _) = CInt 0
> nodeSize (Constr _ vs) = closureNodeSize (length vs)
> nodeSize (Closure _ vs) = closureNodeSize (length vs)
> nodeSize (Lazy f vs) = suspendNodeSize (length vs)
> nodeSize Free = CExpr "variable_node_size"
> nodeSize (Ref _) = error "internal error: nodeSize(Ref)"

> ctypeSize :: CArgType -> CExpr
> ctypeSize TypeBool = CInt 0
> ctypeSize TypeChar = CInt 0
> ctypeSize TypeInt = CExpr "int_node_size"
> ctypeSize TypeFloat = CExpr "float_node_size"
> ctypeSize TypePtr = CExpr "ptr_node_size"
> ctypeSize TypeFunPtr = CExpr "ptr_node_size"
> ctypeSize TypeStablePtr = CExpr "ptr_node_size"

> closureNodeSize, suspendNodeSize :: Int -> CExpr
> closureNodeSize n = CFunCall "closure_node_size" [CInt n]
> suspendNodeSize n = CFunCall "suspend_node_size" [CInt n]

\end{verbatim}
The maximum stack depth of a function is simply the difference between
the number of arguments passed to the function and the number of
arguments pushed onto the stack when calling the continuation. Note
that \texttt{CPSEnter} may push the node to be evaluated onto the
stack. No stack check is performed before a \texttt{CPSApply}
statement because the required stack depth depends on the number of
arguments saved in the closure that is applied. In case of a
\texttt{CPSSwitch} statement, every alternative is responsible for
performing a stack check.
\begin{verbatim}

> stackCheck :: [Name] -> CPSStmt -> [CStmt]
> stackCheck vs st = [CProcCall "CHECK_STACK" [CInt depth] | depth > 0]
>   where depth = stackDepth st - length vs

> stackDepth :: CPSStmt -> Int
> stackDepth (CPSJump k) = length (contVars k)
> stackDepth (CPSReturn _ k) = stackDepthCont k
> stackDepth (CPSEnter _ k) = 1 + stackDepthCont k
> stackDepth (CPSExec _ vs k) = length vs + stackDepthCont k
> stackDepth (CPSApply _ _) = 0
> stackDepth (CPSUnify _ _ k) = length (contVars k)
> stackDepth (CPSDelay _ k) = 1 + length (contVars k)
> stackDepth (CPSDelayNonLocal _ k st) =
>   max (1 + length (contVars k)) (stackDepth st)
> stackDepth (CPSSeq _ st) = stackDepth st
> stackDepth (CPSSwitch _ _ _) = 0
> stackDepth (CPSChoices vk (k:_)) = maybe 1 (const 2) vk + length (contVars k)

> stackDepthCont :: Maybe CPSCont -> Int
> stackDepthCont = maybe 0 (length . contVars)

\end{verbatim}
All constants that are used in a function are preallocated in a static
array \texttt{Node *constants[]} at the beginning of that function.
The following functions compute the set of variables which are bound
to constants together with their respective initializer expressions.
Recall that literals as well as nullary data constructors and partial
applications without arguments are allocated globally in order to
improve sharing.

In order to detect constants in recursive data definitions like
\verb|let { xs=0:ys; ys=1:xs } in |\dots{} efficiently, the
declarations in a let statement were split into minimal binding groups
when the code was transformed into CPS.
\begin{verbatim}

> isConstant :: FM Name CExpr -> Name -> Bool
> isConstant consts v = isJust (lookupFM v consts)

> constants :: [[Bind]] -> FM Name CExpr
> constants dss = fromListFM $ snd $
>   mapAccumL init 0 [(v,n) | ds <- dss, Bind v n <- ds, v `elemSet` vs0]
>   where vs0 = constVars dss
>         init o (v,Lit c) = (o,(v,literal c))
>         init o (v,Constr c vs)
>           | null vs = (o,(v,constRef (constNode c)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Closure f vs)
>           | null vs = (o,(v,constRef (constFunc f)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Ref v') = (o,(v,CExpr (show v')))
>         init _ (v,n) = error ("internal error: constants.init" ++ show n)
>         constant = asNode . add (CExpr constArray) . CInt

> constVars :: [[Bind]] -> Set Name
> constVars = foldl_strict addConst zeroSet
>   where addConst vs0 ds = if all (isConst vs0') ns then vs0' else vs0
>           where vs0' = foldr addToSet vs0 vs
>                 (vs,ns) = unzip [(v,n) | Bind v n <- ds]
>         isConst _ (Lit _) = True
>         isConst vs0 (Constr _ vs) = all (`elemSet` vs0) vs
>         isConst vs0 (Closure _ vs) = all (`elemSet` vs0) vs
>         isConst _ (Lazy _ _) = False
>         isConst _ Free = False
>         isConst vs0 (Ref v) = v `elemSet` vs0

> literal :: Literal -> CExpr
> literal (Char c) = asNode (CAdd (CExpr "char_table") (CInt (ord c)))
> literal (Int i) = CExpr (constInt i)
> literal (Float f) = constRef (constFloat f)

> constDefs :: FM Name CExpr -> [Bind] -> [CStmt]
> constDefs consts ds =
>   [CStaticArray nodeConstPtrType constArray is | not (null is)]
>   where is = constData consts ds

> constData :: FM Name CExpr -> [Bind] -> [CInitializer]
> constData consts ds = map (CInit . asNode) $ foldr constInit [] ds
>   where constInit (Bind v (Constr c vs)) is
>           | not (null vs) && isConstant consts v =
>               CAddr (CExpr (dataInfo c)) : map arg vs ++ is
>         constInit (Bind v (Closure f vs)) is
>           | not (null vs) && isConstant consts v =
>               functionInfo f (length vs) : map arg vs ++ is
>         constInit _ is = is
>         arg v = fromJust (lookupFM v consts)

> allocNode :: FM Name CExpr -> Bind -> [CStmt]
> allocNode consts (Bind v n) =
>   case lookupFM v consts of
>     Just e -> [CLocalVar nodePtrType v' (Just e)]
>     Nothing ->
>       case n of
>         Lit c -> [CLocalVar nodePtrType v' (Just (literal c))]
>         Ref v'' -> [CLocalVar nodePtrType v' (Just (CExpr (show v'')))]
>         _ -> [CLocalVar nodePtrType v' (Just (asNode (CExpr "hp"))),
>               CIncrBy (LVar "hp") (nodeSize n)]
>   where v' = show v

> initNode :: FM Name CExpr -> Bind -> [CStmt]
> initNode _ (Bind v (Lit _)) = []
> initNode consts (Bind v (Constr c vs))
>   | isConstant consts v = []
>   | otherwise = initConstr (LVar (show v)) c (map show vs)
> initNode consts (Bind v (Closure f vs))
>   | isConstant consts v = []
>   | otherwise = initClosure (LVar (show v)) f (map show vs)
> initNode _ (Bind v (Lazy f vs)) = initLazy (LVar (show v)) f (map show vs)
> initNode _ (Bind v Free) = initFree (LVar (show v))
> initNode _ (Bind v (Ref _)) = []

> initConstr :: LVar -> Name -> [String] -> [CStmt]
> initConstr v c vs =
>   CAssign (LField v "info") (CAddr (CExpr (dataInfo c))) :
>   initArgs (LField v "c.args") vs

> initClosure :: LVar -> Name -> [String] -> [CStmt]
> initClosure v f vs =
>   CAssign (LField v "info") (functionInfo f (length vs)) :
>   initArgs (LField v "c.args") vs

> initLazy :: LVar -> Name -> [String] -> [CStmt]
> initLazy v f vs =
>   CAssign (LField v "info") (CExpr (lazyInfoTable f)) :
>   CAssign (LField v "s.spc") (CExpr "ss") :
>   if null vs then
>     [CAssign (LElem (LField v "s.args") (CInt 0)) CNull]
>   else
>     initArgs (LField v "s.args") vs

> initFree :: LVar -> [CStmt]
> initFree v =
>   [CAssign (LField v "info") (CExpr "variable_info_table"),
>    CAssign (LField v "v.spc") (CExpr "ss"),
>    CAssign (LField v "v.wq") CNull,
>    CAssign (LField v "v.cstrs") CNull]

> initArgs :: LVar -> [String] -> [CStmt]
> initArgs v vs = zipWith (initArg v) [0..] vs
>   where initArg v i = CAssign (LElem v (CInt i)) . CExpr

\end{verbatim}
Every abstract machine code statement is translated by its own
translation function.
\begin{verbatim}

> cCode :: FM Name CExpr -> [Name] -> CPSStmt -> [CStmt]
> cCode _ vs0 (CPSJump k) = jump vs0 k
> cCode _ vs0 (CPSReturn v k) = ret vs0 v k
> cCode _ vs0 (CPSEnter v k) = enter vs0 v k
> cCode _ vs0 (CPSExec f vs k) = exec vs0 f vs k
> cCode _ vs0 (CPSApply v vs) = apply vs0 v vs
> cCode _ vs0 (CPSUnify v v' k) = unifyVar vs0 v v' k
> cCode _ vs0 (CPSDelay v k) = delay vs0 v k
> cCode consts vs0 (CPSDelayNonLocal v k st) =
>   delayNonLocal vs0 v k ++ cCode consts vs0 st
> cCode consts vs0 (CPSSeq st1 st2) = cCode0 consts st1 ++ cCode consts vs0 st2
> cCode consts vs0 (CPSSwitch unboxed v cases) =
>   switchOnTerm unboxed vs0 v
>                [(t,caseCode vs0 v t st) | CaseBlock t st <- cases]
> cCode _ vs0 (CPSChoices vk ks) = choices vs0 vk ks

> cCode0 :: FM Name CExpr -> Stmt0 -> [CStmt]
> cCode0 _ (Lock v) = lock v
> cCode0 _ (Update v1 v2) = update v1 v2
> cCode0 _ (Eval _ _) = error "internal error: cCode0"
> cCode0 consts (Let ds) =
>   concatMap (allocNode consts) ds ++ concatMap (initNode consts) ds
> cCode0 _ (CCall _ ty v cc) = cCall ty v cc

> jump :: [Name] -> CPSCont -> [CStmt]
> jump vs0 k = saveVars vs0 (contVars k) ++ [goto (contName k)]

> ret :: [Name] -> Name -> Maybe CPSCont -> [CStmt]
> ret vs0 v Nothing =
>   saveVars vs0 [] ++
>   [CLocalVar labelType "_ret_ip" (Just (CCast labelType (CExpr "sp[0]"))),
>    CAssign (LVar "sp[0]") result,
>    CTrace "%I return %N\n" [result],
>    goto "_ret_ip"]
>   where result = CExpr (show v)
> ret vs0 v (Just k) =
>   saveVars vs0 (v : tail (contVars k)) ++ [goto (contName k)]

> enter :: [Name] -> Name -> Maybe CPSCont -> [CStmt]
> enter vs0 v k =
>   CLocalVar nodePtrType v' (Just (CExpr (show v))) :
>   tagSwitch (Name v') [] (Just [])
>             [CCase "FAPP_TAG" [{- fall through! -}],
>              CCase "SUSPEND_TAG" [{- fall through! -}],
>              CCase "QUEUEME_TAG"
>                    (saveCont vs0 [Name v'] k ++
>                     [gotoExpr (field v' "info->eval")])] :
>   ret vs0 (Name v') k
>   where v' = "_node"

> exec :: [Name] -> Name -> [Name] -> Maybe CPSCont -> [CStmt]
> exec vs0 f vs k = saveCont vs0 vs k ++ [goto (cName f)]

> saveCont :: [Name] -> [Name] -> Maybe CPSCont -> [CStmt]
> saveCont vs0 vs Nothing = saveVars vs0 vs
> saveCont vs0 vs (Just k) =
>   CLocalVar nodePtrType ip (Just (asNode (CExpr (contName k)))) :
>   saveVars vs0 (vs ++ Name ip : tail (contVars k))
>   where ip = "_cont_ip"

> lock :: Name -> [CStmt]
> lock v =
>   [rtsAssertList[isBoxed v',CRel (nodeTag v') "==" (CExpr "SUSPEND_TAG"),
>                  CFunCall "is_local_space" [field v' "s.spc"]],
>    CIf (CRel (CCast wordPtrType (CExpr v')) "<" (CExpr "hlim"))
>        [procCall "DO_SAVE" [v',"q.wq"],
>         CIncrBy (LField (LVar v') "info") (CInt 1)]
>        [CAssign (LField (LVar v') "info") (CExpr "queueMe_info_table")],
>    CAssign (LField (LVar v') "q.wq") CNull]
>   where v' = show v

> update :: Name -> Name -> [CStmt]
> update v1 v2 =
>   [rtsAssertList[isBoxed v1',CRel (nodeTag v1') "==" (CExpr "QUEUEME_TAG"),
>                  CFunCall "is_local_space" [field v1' "q.spc"]],
>    CLocalVar (CType "ThreadQueue") wq (Just (CField (CExpr v1') "q.wq")),
>    procCall "SAVE" [v1',"q.wq"],
>    CIncrBy (LField (LVar v1') "info") (CInt 1),
>    CAssign (LField (LVar v1') "n.node") (CExpr (show v2)),
>    CIf (CExpr wq) [procCall "wake_threads" [wq]] []]
>   where v1' = show v1
>         wq = "wq"

> unifyVar :: [Name] -> Name -> Name -> CPSCont -> [CStmt]
> unifyVar vs0 v n k =
>   saveVars vs0 [if v == v' then n else v' | v' <- contVars k] ++
>   [tailCall "bind_var" [show v,show n,contName k]]

> delay :: [Name] -> Name -> CPSCont -> [CStmt]
> delay vs0 v k = saveCont vs0 [v] (Just k) ++ [goto "sync_var"]

> delayNonLocal :: [Name] -> Name -> CPSCont -> [CStmt]
> delayNonLocal vs0 v k =
>   [CIf (CFunCall "!is_local_space" [field (show v) "v.spc"])
>        (delay vs0 v k)
>        []]

> choices :: [Name] -> Maybe (Name,CPSCont) -> [CPSCont] -> [CStmt]
> choices vs0 vk (k:ks) =
>   CStaticArray constLabelType choices
>                (map (CInit . CExpr . contName) (k:ks) ++ [CInit CNull]) :
>   CLocalVar nodePtrType ips (Just (asNode (CExpr choices))) :
>   saveVars vs0 (Name ips : contVars k) ++
>   [CppCondStmts "YIELD_NONDET"
>      [CIf (CExpr "rq") (yieldCall vk) []]
>      [],
>    goto "nondet_handlers->choices"]
>   where ips = "_choice_ips"
>         choices = "_choices"
>         yieldCall (Just (v,k')) =
>           saveCont (Name ips : contVars k) [v,Name ips] (Just k') ++
>           [tailCall "yield_delay_thread" ["flex_yield_resume",show v]]
>         yieldCall Nothing =
>           [tailCall "yield_thread" ["nondet_handlers->choices"]]

> failAndBacktrack :: [CStmt]
> failAndBacktrack = [goto "nondet_handlers->fail"]

\end{verbatim}
Code generation for \texttt{CPSSwitch} statements is a little bit more
complicated because matching literal constants requires two nested
switches. The outer switch matches the common tag and the inner switch
the literal's value. Furthermore, integer literals are either encoded
in the pointer or stored in a heap allocated node depending on their
value and the setting of the preprocessor constant
\texttt{ONLY\_BOXED\_OBJECTS}, which forces heap allocation of all
integer numbers when set to a non-zero value.
\begin{verbatim}

> switchOnTerm :: Bool -> [Name] -> Name -> [(CPSTag,[CStmt])] -> [CStmt]
> switchOnTerm maybeUnboxed vs0 v cases =
>   tagSwitch v [updVar vs0 v] unboxedCase otherCases :
>   head (dflts ++ [failAndBacktrack])
>   where v' = show v
>         (lits,constrs,vars,dflts) = foldr partition ([],[],[],[]) cases
>         (chars,ints,floats) = foldr litPartition ([],[],[]) lits
>         unboxedCase
>           | maybeUnboxed =
>               Just [CppCondStmts "ONLY_BOXED_OBJECTS"
>                       [CProcCall "curry_panic"
>                                  [CString "impossible: is_unboxed(%p)\n",
>                                   CExpr v']]
>                       [intSwitch (funCall "unboxed_val" [v']) ints]
>                    | not (null ints)]
>           | otherwise = Nothing
>         otherCases =
>           map varCase vars ++ [charCase | not (null chars)] ++
>           [intCase | not (null ints)] ++ [floatCase | not (null floats)] ++
>           map constrCase constrs
>         varCase = CCase "VARIABLE_TAG"
>         charCase = CCase "CHAR_TAG" [charSwitch v chars,CBreak]
>         intCase =
>           CCase "INT_TAG"
>                 [intSwitch (CField (CExpr v') "i.i") ints,CBreak]
>         floatCase = CCase "FLOAT_TAG" (floatSwitch v floats ++ [CBreak])
>         constrCase (c,stmts) = CCase (dataTag c) stmts
>         partition (t,stmts) ~(lits,constrs,vars,dflts) =
>           case t of
>              CPSLitCase l -> ((l,stmts) : lits,constrs,vars,dflts)
>              CPSConstrCase c _ -> (lits,(c,stmts) : constrs,vars,dflts)
>              CPSFreeCase -> (lits,constrs,stmts : vars,dflts)
>              CPSDefaultCase -> (lits,constrs,vars,stmts : dflts)
>         litPartition (Char c,stmts) ~(chars,ints,floats) =
>           ((c,stmts):chars,ints,floats)
>         litPartition (Int i,stmts) ~(chars,ints,floats) =
>           (chars,(i,stmts):ints,floats)
>         litPartition (Float f,stmts) ~(chars,ints,floats) =
>           (chars,ints,(f,stmts):floats)

> tagSwitch :: Name -> [CStmt] -> Maybe [CStmt] -> [CCase] -> CStmt
> tagSwitch v upd unboxed cases =
>   CLoop [unboxedSwitch unboxed (CSwitch (nodeTag v') allCases),CBreak]
>   where v' = show v
>         allCases =
>           CCase "INDIR_TAG"
>             (CAssign (LVar v') (field v' "n.node") : upd ++ [CContinue]) :
>           cases ++
>           [CDefault [CBreak]]
>         unboxedSwitch (Just sts) switch
>           | null sts = CIf (isBoxed v') [switch] []
>           | otherwise = CIf (isUnboxed v') sts [switch]
>         unboxedSwitch Nothing switch = switch

> charSwitch :: Name -> [(Char,[CStmt])] -> CStmt
> charSwitch v cases =
>   CSwitch (CField (CExpr (show v)) "ch.ch")
>           ([CCase (show (ord c)) stmts | (c,stmts) <- cases] ++
>            [CDefault [CBreak]])

> intSwitch :: CExpr -> [(Int,[CStmt])] -> CStmt
> intSwitch e cases =
>   CSwitch e
>     ([CCase (show i) stmts | (i,stmts) <- cases] ++ [CDefault [CBreak]])

> floatSwitch :: Name -> [(Double,[CStmt])] -> [CStmt]
> floatSwitch v cases =
>   getFloat "d" (field (show v) "f") ++ foldr (match (CExpr "d")) [] cases
>   where match v (f,stmts) rest = [CIf (CRel v "==" (CFloat f)) stmts rest]

\end{verbatim}
The code for the \texttt{CPSApply} statement has to check the number
of missing arguments of the closure being applied. If there are too
few arguments, a new closure node is returned for the partial
application. Otherwise, the application is evaluated by pushing the
closure's arguments onto the stack and jumping to the function's
entry point. If the closure is applied to too many arguments, the code
generated by \texttt{applyExec} creates a return frame in the stack
such that the result of the application is applied to the remaining
arguments.
\begin{verbatim}

> apply :: [Name] -> Name -> [Name] -> [CStmt]
> apply vs0 v vs =
>   CLocalVar uintType "argc" (Just (funCall "closure_argc" [v'])) :
>   assertRel (arity v') ">" (CExpr "argc") :
>   CLocalVar uintType "miss" (Just (CSub (arity v') (CExpr "argc"))) :
>   CIf (CRel (CExpr "miss") ">" (CInt n)) (applyPartial vs0 n v) [] :
>   applyExec n v
>   where v' = show v
>         n = length vs
>         arity v = CField (CExpr v) "info->arity"

> applyPartial :: [Name] -> Int -> Name -> [CStmt]
> applyPartial vs0 n v =
>   CLocalVar uintType "sz" (Just (funCall "node_size" [v'])) :
>   CProcCall "CHECK_HEAP" [CAdd (CExpr "sz") (CInt n)] :
>   CAssign (LVar v') (asNode (CExpr "hp")) :
>   CIncrBy (LVar "hp") (CAdd (CExpr "sz") (CInt n)) :
>   wordCopy (CExpr v') (CExpr "sp[0]") "sz" :
>   CIncrBy (LField (LVar v') "info") (CInt n) :
>   [CAssign (LElem (LField (LVar v') "c.args") (CAdd (CExpr "argc") (CInt i)))
>            (CElem (CExpr "sp") (CInt (i+1))) | i <- [0 .. n-1]] ++
>   ret vs0 v Nothing
>   where v' = show v

> applyExec :: Int -> Name -> [CStmt]
> applyExec n v =
>   [CIf (CRel (CExpr "miss") "==" (CInt n))
>        [CIncrBy (LVar "sp") (CInt 1),
>         CIf (CExpr "argc > 1") [procCall "CHECK_STACK" ["argc"]] []]
>        [CIf (CExpr "argc > 0") [procCall "CHECK_STACK" ["argc"]] [],
>         wordCopy (CExpr "sp") (CAdd (CExpr "sp") (CInt 1)) "miss",
>         CStaticArray constLabelType applyTable
>                      [CInit (CExpr (cName (apName i))) | i <- [n,n-1..2]],
>         CAssign (LElem (LVar "sp") (CExpr "miss"))
>                 (asNode (CElem (CExpr applyTable)
>                                (CSub (CExpr "miss") (CInt 1))))],
>    CDecrBy (LVar "sp") (CExpr "argc"),
>    wordCopy (CExpr "sp") (CField (CExpr v') "c.args") "argc",
>    gotoExpr (field v' "info->entry")]
>   where v' = show v

\end{verbatim}
For a foreign function call, the generated code first unboxes all
arguments, then calls the function, and finally boxes the result of
the call. When taking the address of a foreign variable, the code
first loads this address into a temporary variable and then boxes it.
\begin{verbatim}

> cCall :: CRetType -> Name -> CCall -> [CStmt]
> cCall ty v cc = cEval ty v' cc ++ box ty (show v) v'
>   where v' = "_cret"

> cEval :: CRetType -> String -> CCall -> [CStmt]
> cEval ty v (StaticCall f xs) = cFunCall ty v f xs
> cEval ty v1 (DynamicCall v2 xs) =
>   unboxFunPtr ty (map fst xs) f (show v2) : cFunCall ty v1 f xs
>   where f = "_cfun"
> cEval ty v (StaticAddr x) = cAddr ty v x

> cFunCall :: CRetType -> String -> String -> [(CArgType,Name)] -> [CStmt]
> cFunCall ty v f xs =
>   concat [unbox ty v2 (show v1) | ((ty,v1),v2) <- zip xs vs] ++
>   [callCFun ty v f vs]
>   where vs = ["_carg" ++ show i | i <- [1..length xs]]

> cAddr :: CRetType -> String -> String -> [CStmt]
> cAddr Nothing v x = []
> cAddr (Just ty) v x =
>   [CLocalVar (ctype ty) v (Just (CCast (ctype ty) (CAddr (CExpr x))))]

> unbox :: CArgType -> String -> String -> [CStmt]
> unbox TypeBool v1 v2 =
>   [CLocalVar (ctype TypeBool) v1 (Just (CField (CExpr v2) "info->tag"))]
> unbox TypeChar v1 v2 =
>   [CLocalVar (ctype TypeChar) v1 (Just (CField (CExpr v2) "ch.ch"))]
> unbox TypeInt v1 v2 =
>   [CLocalVar (ctype TypeInt) v1 (Just (funCall "long_val" [v2]))]
> unbox TypeFloat v1 v2 = getFloat v1 (CField (CExpr v2) "f")
> unbox TypePtr v1 v2 =
>   [CLocalVar (ctype TypePtr) v1 (Just (CField (CExpr v2) "p.ptr"))]
> unbox TypeFunPtr v1 v2 =
>   [CLocalVar (ctype TypeFunPtr) v1 (Just (CField (CExpr v2) "p.ptr"))]
> unbox TypeStablePtr v1 v2 =
>   [CLocalVar (ctype TypeStablePtr) v1 (Just (CField (CExpr v2) "p.ptr"))]

> unboxFunPtr :: CRetType -> [CArgType] -> String -> String -> CStmt
> unboxFunPtr ty0 tys v1 v2 =
>   CLocalVar ty v1 (Just (CCast ty (CField (CExpr v2) "p.ptr")))
>   where ty = CPointerType
>            $ CFunctionType (maybe voidType ctype ty0) (map ctype tys)

> callCFun :: CRetType -> String -> String -> [String] -> CStmt
> callCFun Nothing _ f vs = procCall f vs
> callCFun (Just ty) v f vs = CLocalVar (ctype ty) v (Just (funCall f vs))

> box :: CRetType -> String -> String -> [CStmt]
> box Nothing v _ =
>   [CLocalVar nodePtrType v (Just (constRef (constNode (mangle "()"))))]
> box (Just TypeBool) v1 v2 =
>   [CLocalVar nodePtrType v1
>              (Just (CCond (CExpr v2) (const prelTrue) (const prelFalse)))]
>   where const = constRef . constNode
> box (Just TypeChar) v1 v2 =
>   [CLocalVar nodePtrType v1
>              (Just (asNode (CAdd (CExpr "char_table")
>                                  (CRel (CExpr v2) "&" (CInt 0xff)))))]
> box (Just TypeInt) v1 v2 =
>   [CLocalVar nodePtrType v1 Nothing,
>    CIf (funCall "is_large_int" [v2])
>      [CAssign (LVar v1) (asNode (CExpr "hp")),
>       CAssign (LField (LVar v1) "info") (CAddr (CExpr "int_info")),
>       CAssign (LField (LVar v1) "i.i") (CExpr v2),
>       CIncrBy (LVar "hp") (ctypeSize TypeInt)]
>      [CppCondStmts "ONLY_BOXED_OBJECTS"
>         [CProcCall "curry_panic"
>                    [CString "impossible: !is_large_int(%ld)\n",CExpr v2]]
>         [CAssign (LVar v1) (funCall "mk_unboxed" [v2])]]]
> box (Just TypeFloat) v1 v2 =
>   [CLocalVar nodePtrType v1 (Just (asNode (CExpr "hp"))),
>    CAssign (LField (LVar v1) "info") (CAddr (CExpr  "float_info")),
>    CProcCall "put_double_val" [CField (CExpr v1) "f",CExpr v2],
>    CIncrBy (LVar "hp") (ctypeSize TypeFloat)]
> box (Just TypePtr) v1 v2 =
>   [CLocalVar nodePtrType v1 Nothing,
>    CIf (CRel (CExpr v2) "==" CNull)
>      [CAssign (LVar v1) (constRef "null_ptr")]
>      [CAssign (LVar v1) (asNode (CExpr "hp")),
>       CAssign (LField (LVar v1) "info") (CAddr (CExpr "ptr_info")),
>       CAssign (LField (LVar v1) "p.ptr") (CExpr v2),
>       CIncrBy (LVar "hp") (ctypeSize TypePtr)]]
> box (Just TypeFunPtr) v1 v2 =
>   [CLocalVar nodePtrType v1 Nothing,
>    CIf (CRel (CExpr v2) "==" CNull)
>      [CAssign (LVar v1) (constRef "null_funptr")]
>      [CAssign (LVar v1) (asNode (CExpr "hp")),
>       CAssign (LField (LVar v1) "info") (CAddr (CExpr "funptr_info")),
>       CAssign (LField (LVar v1) "p.ptr") (CExpr v2),
>       CIncrBy (LVar "hp") (ctypeSize TypeFunPtr)]]
> box (Just TypeStablePtr) v1 v2 =
>   [CLocalVar nodePtrType v1 Nothing,
>    CIf (CRel (CExpr v2) "==" CNull)
>      [CAssign (LVar v1) (constRef "null_stabptr")]
>      [CAssign (LVar v1) (asNode (CExpr "hp")),
>       CAssign (LField (LVar v1) "info") (CAddr (CExpr "stabptr_info")),
>       CAssign (LField (LVar v1) "p.ptr") (CExpr v2),
>       CIncrBy (LVar "hp") (ctypeSize TypeStablePtr)]]

> ctype :: CArgType -> CType
> ctype TypeBool = intType
> ctype TypeChar = intType
> ctype TypeInt = longType
> ctype TypeFloat = doubleType
> ctype TypePtr = voidPtrType
> ctype TypeFunPtr = voidPtrType
> ctype TypeStablePtr = voidPtrType

\end{verbatim}
As a convenience to the user, we strip the decoration of auxiliary
function names introduced by the debugging transformation when the
name of a function is printed. In particular, the debugger adds the
prefix \texttt{\_debug\#} and a suffix \texttt{\#}$n$ to the name of
the transformed function. Note that the prefix is added to the
unqualified name.
\begin{verbatim}

> undecorate :: String -> String
> undecorate cs =
>   case break ('_' ==) cs of
>     (cs', "") -> dropSuffix cs'
>     (cs', ('_':cs''))
>       | "debug#" `isPrefixOf` cs'' -> cs' ++ undecorate (drop 6 cs'')
>       | otherwise -> cs' ++ '_' : undecorate cs''
>   where dropSuffix cs =
>           case break ('#' ==) cs of
>             (cs',"") -> cs'
>             (cs','#':cs'')
>               | all isDigit cs'' -> cs'
>               | otherwise -> cs' ++ '#' : dropSuffix cs''

\end{verbatim}
In order to avoid some trivial name conflicts with the standard C
library, the names of all Curry functions are prefixed with two
underscores. The integer key of each CPS function is added to the
name, except for the function's main entry point, whose key is
\texttt{0}.

The names of the info vector for a data constructor application and
the info table for a function are constructed by appending the
suffixes \texttt{\_info} and \texttt{\_info\_table}, respectively, to
the name. The suffixes \texttt{\_const} and \texttt{\_function} are
used for constant constructors and functions, respectively.
\begin{verbatim}

> cName :: Name -> String
> cName x = "__" ++ show x

> cPrivName :: Name -> Int -> String
> cPrivName f n
>   | n == 0 = cName f
>   | otherwise = cName f ++ '_' : show n

> cpsName :: CPSFunction -> String
> cpsName (CPSFunction f n _ _) = cPrivName f n

> contName :: CPSCont -> String
> contName (CPSCont f) = cpsName f

> constArray, applyTable :: String
> constArray = "constants"
> applyTable = "apply_table"

> evalFunc, lazyFunc :: Name -> String
> evalFunc f = cName f ++ "_eval"
> lazyFunc f = cName f ++ "_lazy"

> dataInfo, infoTable, lazyInfoTable :: Name -> String
> dataInfo c = cName c ++ "_info"
> infoTable f = cName f ++ "_info_table"
> lazyInfoTable f = cName f ++ "_lazy_info_table"

> functionInfo :: Name -> Int -> CExpr
> functionInfo f n
>   | isAp f = CAddr (CExpr (dataInfo f))
>   | otherwise = add (CExpr (infoTable f)) (CInt n)

> dataTag :: Name -> String
> dataTag c = cName c ++ "_tag"

> closVar :: Name -> String
> closVar v = show v ++ "_clos"

\end{verbatim}
The function \texttt{tupleArity} computes the arity of a tuple
constructor by counting the commas in the -- demangled -- name. Note
that \texttt{()} is \emph{not} a tuple name.
\begin{verbatim}

> isTuple :: Name -> Bool
> isTuple c = isTupleName (demangle c)
>   where isTupleName ('(':',':cs) = dropWhile (',' ==) cs == ")"
>         isTupleName _ = False

> tupleArity :: Name -> Int
> tupleArity c = arity (demangle c)
>   where arity ('(':',':cs)
>           | cs'' == ")" = length cs' + 2
>           where (cs',cs'') = span (',' ==) cs
>         arity _ = error "internal error: tupleArity"

\end{verbatim}
The function \texttt{apArity} returns the arity of an application
function \texttt{@}$_n$. Note that \texttt{@}$_n$ has arity $n+1$
since $n$ denotes the arity of its first argument. The function
\texttt{apName} is the inverse of \texttt{apArity}, i.e., the
following two equations hold
\begin{eqnarray*}
  i & = & \texttt{apArity}(\texttt{apName}(i)) \\
  x & = & \texttt{apName}(\texttt{apArity}(x))
\end{eqnarray*}
provided that $x$ is the name of an application function. Note the
special case for \texttt{@}, which is used instead of \texttt{@}$_1$.
\begin{verbatim}

> isAp :: Name -> Bool
> isAp f = isApName (demangle f)
>   where isApName ('@':cs) = all isDigit cs
>         isApName _ = False

> apArity :: Name -> Int
> apArity f = arity (demangle f)
>   where arity ('@':cs)
>           | null cs = 2
>           | all isDigit cs = read cs + 1
>         arity _ = error "internal error: applyArity"

> apName :: Int -> Name
> apName n = mangle ('@' : if n == 2 then "" else show (n - 1))

> constChar :: Char -> String
> constChar c = "char_table[" ++ show (ord c) ++ "]"

> constInt :: Int -> String
> constInt i = "int_" ++ mangle (show i)
>   where mangle ('-':cs) = 'M':cs
>         mangle cs = cs

> constFloat :: Double -> String
> constFloat f = "float_" ++ map mangle (show f)
>   where mangle '+' = 'P'
>         mangle '-' = 'M'
>         mangle '.' = '_'
>         mangle c = c

> constNode, constFunc :: Name -> String
> constNode c = cName c ++ "_node"
> constFunc f = cName f ++ "_function"

\end{verbatim}
Here are some convenience functions, which simplify the construction
of the abstract syntax tree.
\begin{verbatim}

> asNode :: CExpr -> CExpr
> asNode = CCast nodePtrType

> goto :: String -> CStmt
> goto l = gotoExpr (CExpr l)

> gotoExpr :: CExpr -> CStmt
> gotoExpr l = CProcCall "GOTO" [l]

> tailCall :: String -> [String] -> CStmt
> tailCall f xs = gotoExpr (funCall f xs)

> funCall :: String -> [String] -> CExpr
> funCall f xs = CFunCall f (map CExpr xs)

> procCall :: String -> [String] -> CStmt
> procCall f xs = CProcCall f (map CExpr xs)

> wordCopy :: CExpr -> CExpr -> String -> CStmt
> wordCopy e1 e2 sz =
>   CProcCall "memcpy" [e1,e2,CExpr sz `CMul` CExpr "word_size"]

> rtsAssert :: CExpr -> CStmt
> rtsAssert e = CProcCall "ASSERT" [e]

> rtsAssertList :: [CExpr] -> CStmt
> rtsAssertList es = rtsAssert (foldr1 (flip CRel "&&") es)

> assertRel :: CExpr -> String -> CExpr -> CStmt
> assertRel x op y = rtsAssert (CRel x op y)

> add :: CExpr -> CExpr -> CExpr
> add (CInt 0) y = y
> add x (CInt 0) = x
> add x y = x `CAdd` y

> getFloat :: String -> CExpr -> [CStmt]
> getFloat v e =
>   [CLocalVar doubleType v Nothing,CProcCall "get_double_val" [CExpr v,e]]

> constRef :: String -> CExpr
> constRef = asNode . CAddr . CExpr

> isBoxed, isUnboxed :: String -> CExpr
> isBoxed v = funCall "is_boxed" [v]
> isUnboxed v = funCall "is_unboxed" [v]

> nodeTag :: String -> CExpr
> nodeTag v = field v "info->tag"

> field :: String -> String -> CExpr
> field v f = CField (CExpr v) f

\end{verbatim}
Frequently used types.
\begin{verbatim}

> intType, longType, uintType, ulongType, doubleType :: CType
> intType = CType "int"
> longType = CType "long"
> uintType = CType "unsigned int"
> ulongType = CType "unsigned long"
> doubleType = CType "double"

> voidType, voidPtrType :: CType
> voidType = CType "void"
> voidPtrType = CPointerType voidType

> wordPtrType :: CType
> wordPtrType = CPointerType (CType "word")

> labelType, constLabelType :: CType
> labelType = CType "Label"
> constLabelType = CConstType "Label"

> nodeType, nodePtrType, nodeConstPtrType :: CType
> nodeType = CType "Node"
> nodePtrType = CPointerType nodeType
> nodeConstPtrType = CConstPointerType nodeType

> nodeInfoType, nodeInfoConstPtrType :: CType
> nodeInfoType = CType "NodeInfo"
> nodeInfoConstPtrType = CConstPointerType nodeInfoType

\end{verbatim}
We make use of some prelude entities in the generated code.
\begin{verbatim}

> prelName :: String -> Name
> prelName x = mangleQualified ("prelude." ++ x)

> prelTrue, prelFalse :: Name
> prelTrue = prelName "True"
> prelFalse = prelName "False"

\end{verbatim}
