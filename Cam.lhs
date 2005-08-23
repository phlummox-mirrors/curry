% -*- LaTeX -*-
% $Id: Cam.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Cam.lhs}
\section{Abstract Machine Code}
This section describes the instruction set of the abstract machine.
\begin{verbatim}

> module Cam where
> import Char

\end{verbatim}
An abstract machine code module consists of a list of import, data,
and function declarations. A data declaration names the constructors
of a data type together with their arity. A function declaration
comprises the function's name, arguments, and code.
\begin{verbatim}

> type Module = [Decl]
> data Decl =
>     ImportDecl Name
>   | DataDecl Name [ConstrDecl]
>   | FunctionDecl Name [Name] Stmt
>   deriving (Eq,Show)
> data ConstrDecl = ConstrDecl Name Int deriving (Eq,Show)

> splitCam :: Module -> ([Name],[(Name,[ConstrDecl])],[(Name,[Name],Stmt)])
> splitCam = foldr split ([],[],[])
>   where split (ImportDecl m) ~(ms,ds,fs) = (m:ms,ds,fs)
>         split (DataDecl t cs) ~(ms,ds,fs) = (ms,(t,cs):ds,fs)
>         split (FunctionDecl f n is) ~(ms,dss,fs) = (ms,dss,(f,n,is):fs)

\end{verbatim}
\subsection{Instruction Set}
The instruction set of the abstract machine is a simple block
structured language, which is related to that of the STG and JUMP
machines~\cite{Peyton92:STG, ChakravartyLock97:Jump}. However, in
contrast to these abstract machines, evaluation of nodes is made
explicit in the Curry abstract machine, similar to the code used by
the GRIN project~\cite{BoquistJohnsson96:GRIN, Boquist99:Thesis}.

In our abstract machine language, we distinguish two kinds of
statements. The statements \verb|Return|, \verb|Enter|, \verb|Exec|,
\verb|Seq|, \verb|Switch|, and \verb|Choices| compute a value; the
remaining statements do not compute a value. The body of a function is
always a value computing statement.

\verb|Return|~$x$ returns the address of the node bound to $x$.

\verb|Enter|~$x$ evaluates the node bound to $x$ to head normal form
and returns its address. If the node is already in head normal form,
\verb|Enter|~$x$ is equivalent to \verb|Return|~$x$.

\verb|Exec|~$f(x_1,\dots,x_k)$, where $k$ is the arity of $f$, enters
the global function $f$ and passes the nodes referenced by $x_1$,
\dots, $x_k$ as arguments to it.

\verb|Seq|~\emph{stmt$_1$}~\emph{stmt$_2$} implements sequencing of
statements. It executes \emph{stmt$_1$} and \emph{stmt$_2$} in that
order. Note that \emph{stmt$_1$} must not compute a value. However, it
may introduce new variables (see \verb|Eval| and \verb|Let| below).

\verb|Switch|~\emph{rf}~$x$~\emph{cases} analyzes the node bound to
$x$ and executes the matching case from \emph{cases}. When $x$ is
bound to a free variable, it is non-deterministically instantiated to
the patterns of the \emph{cases} if \emph{rf} is \verb|Flex|, whereas
the current thread is suspended until the variable is bound if
\emph{rf} is \verb|Rigid|.

\verb|Choices|~\emph{alts} non-deterministically executes the
alternatives \emph{alts}.

\verb|Eval|~$x$~\emph{stmt} executes the (value computing) statement
\emph{stmt} and binds its result to the (fresh) variable $x$.

New nodes are allocated and bound with a \verb|Let|~\emph{binds}
statement. The bindings in a \verb|Let| statement may be mutually
recursive.

The statements \verb|Lock|~$x$ and \verb|Update|~$x$~$y$ are used for
implementing the pattern binding update strategy. \verb|Lock|~$x$
overwrites the node bound to $x$ with a queue-me node, and
\verb|Update|~$x$~$y$ overwrites the node bound to $x$ with a pointer
to $y$. $x$ must be bound to a local, unevaluated suspension node when
\verb|Lock| is executed, and to a local queue-me node when
\verb|Update| is executed.

\verb|CCall|~$h$~\emph{ty}~$x$~\emph{cc} binds the variable $x$ to the
result of evaluating the C code \emph{cc}. \emph{cc} is either a
static function call $f((\emph{ty}_1)x_1,\dots,(\emph{ty}_k)x_k)$, a
dynamic function call $(*x)((\emph{ty}_1)x_1,\dots,(\emph{ty}_k)x_k)$,
or the address of a variable \verb|&|$y$. The type \emph{ty} specifies
the type of \emph{cc} and $\emph{ty}_1$, \dots, $\emph{ty}_k$ specify
the types of the arguments $x_1$, \dots, $x_k$. \emph{ty} should be
either \verb|TypePtr| or \verb|TypeFunPtr| when computing the address
of a variable. If \emph{ty} is omitted, the C function is assumed to
return no result and $x$ is bound to \verb|()| after the call. $h$
optionally specifies the name of a C header file, which contains a
prototype of $f$ and a declaration of $y$, respectively.
\begin{verbatim}

> data Stmt =
>     Return Name
>   | Enter Name
>   | Exec Name [Name]
>   | Seq Stmt0 Stmt
>   | Switch RF Name [Case]
>   | Choices [Alt]
>   deriving (Eq,Show)
> data Stmt0 =
>     Lock Name
>   | Update Name Name
>   | Eval Name Stmt
>   | Let [Bind]
>   | CCall (Maybe String) CRetType Name CCall
>   deriving (Eq,Show)

> type Alt = Stmt
> data Bind = Bind Name Expr deriving (Eq,Show)
> data RF = Rigid | Flex deriving (Eq,Show)
> data CCall =
>     StaticCall String [(CArgType,Name)]
>   | DynamicCall Name [(CArgType,Name)]
>   | StaticAddr String
>   deriving (Eq,Show)

\end{verbatim}
The abstract machine supports literal constants, data constructors,
function closures (including partial applications), and logic
variables as nodes. As in the STG machine, we distinguish
non-updatable \verb|Closure| and updatable \verb|Lazy| application
nodes.

The \verb|Ref|~$x$ expression does not denote a fresh node, but a
reference to the node bound to $x$. An abstract machine program can
always be translated into an equivalent program which does not use
\verb|Ref|s. They are useful during the compilation, though.
\begin{verbatim}

> data Literal = Char Char | Int Int | Float Double deriving (Eq,Show)

> data Expr =
>     Lit Literal
>   | Constr Name [Name]
>   | Closure Name [Name]
>   | Lazy Name [Name]
>   | Free
>   | Ref Name
>   deriving (Eq,Show)

\end{verbatim}
Each case of a switch statement associates a pattern with a statement.
The patterns are either literal constants or a data constructor
patterns. In the latter case, the names in a pattern are bound to the
corresponding arguments of the data constructor before executing its
associated statement. A default pattern allows matching all remaining
cases in a switch statement.
\begin{verbatim}

> data Case = Case Tag Stmt deriving (Eq,Show)
> data Tag = LitCase Literal | ConstrCase Name [Name] | DefaultCase
>            deriving (Eq,Show)

\end{verbatim}
Argument and result types of C functions are restricted to booleans,
characters, integer numbers, floating-point numbers, and (untyped)
pointers and function pointers at present. The result type of a C
function may be omitted when the function is called only for its side
effect. In this case, the abstract machine will use the unit
constructor \verb|()| as result of the call.
\begin{verbatim}

> type CRetType = Maybe CArgType
> data CArgType =
>     TypeBool | TypeChar | TypeInt | TypeFloat
>   | TypePtr | TypeFunPtr | TypeStablePtr
>   deriving (Eq,Show)

\end{verbatim}
\subsection{External Names}
External names in the abstract machine code must be composed of
characters and underscores. Therefore the names of Curry operators
have to be encoded. We use the following strategy for mangling Curry
identifiers. All alpha-numeric characters in an identifier are left
unchanged, all other characters are replaced by sequences composed of
an underscore character, the (decimal) character code, and another
underscore character. As a minor exception from this rule, the dot
separating the module name from the unqualified name in a qualified
identifier is replaced by two consecutive underscores.
\begin{verbatim}

> newtype Name = Name String deriving (Eq,Ord)
> instance Show Name where
>   showsPrec _ (Name name) = showString name

\end{verbatim}
The mangling strategy is implemented by the functions \texttt{mangle}
and \texttt{mangleQualified} below. The inverse operation is
implemented by the function \texttt{demangle}.
\begin{verbatim}

> mangle :: String -> Name
> mangle cs = Name (mangleIdent cs)
>   where mangleIdent [] = []
>         mangleIdent (c:cs)
>           | isAlphaNum c = c : mangleIdent cs
>           | otherwise = '_' : show (ord c) ++ '_' : mangleIdent cs

> mangleQualified :: String -> Name
> mangleQualified cs
>   | null mname = Name name'
>   | otherwise = Name (mname' ++ "__" ++ name')
>   where (mname,name) = splitQualified cs
>         Name mname' = mangle mname
>         Name name'  = mangle name

> demangle :: Name -> String
> demangle (Name cs) = demangleName cs
>   where demangleName [] = []
>         demangleName (c:cs)
>           | c == '_' = unescape ds cs'
>           | otherwise = c : demangleName cs
>           where (ds,cs') = span isDigit cs
>         unescape ds ('_':cs)
>           | null ds = '.' : demangleName cs
>           | n <= ord maxBound = chr n : demangleName cs
>           | otherwise = '_' : ds ++ '_' : demangleName cs
>           where n = read ds
>         unescape ds cs = '_':ds ++ demangleName cs

\end{verbatim}
In order to split a qualified name into its module prefix and the
unqualified name, the function \texttt{splitQualified} assumes that
valid module identifiers have to start with an alphabetic character
and that the unqualified name must not be empty.

\ToDo{The heuristics implemented by \texttt{splitQualified} fails for
lifted local functions, as the compiler prefixes their names with the
names of the enclosing functions and uses a dot as separator.}
\begin{verbatim}

> splitQualified :: String -> (String,String)
> splitQualified [] = ([],[])
> splitQualified (c:cs)
>   | isAlpha c =
>       case break ('.' ==) cs of
>         (_,[]) -> ([],c:cs)
>         (prefix,'.':cs')
>           | null cs' || isDigit (head cs') -> ([],c:cs)
>           | otherwise -> (c:prefix `sep` prefix',name)
>           where (prefix',name) = splitQualified cs'
>                 sep cs1 cs2
>                   | null cs2 = cs1
>                   | otherwise = cs1 ++ '.':cs2
>   | otherwise = ([],c:cs)

\end{verbatim}
\input{CamPP.lhs} % \subsection{Pretty-printing Abstract Machine Code}
\input{CamParser.lhs} % \subsection{Parsing Abstract Machine Code}
