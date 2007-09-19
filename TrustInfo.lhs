% -*- LaTeX -*-
% $Id: TrustInfo.lhs 2472 2007-09-19 14:55:02Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TrustInfo.lhs}
\section{Trusted Functions}
The compiler collects trust annotations from the source code in an
environment. A simple environment mapping unqualified names onto
annotations is sufficient because trust annotations control how
function declarations are transformed when generating code for the
declarative debugger (cf.\ Sect.~\ref{sec:dtrans}).
\begin{verbatim}

> module TrustInfo where
> import Curry
> import Env

> type TrustEnv = Env Ident Trust

\end{verbatim}
