% -*- LaTeX -*-
% $Id: PredefIdent.lhs 2461 2007-09-07 08:55:15Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PredefIdent.lhs}
\section{Predefined Identifiers}
This module defines predefined identifiers used at various places in
the compiler.

The function \texttt{lambdaId} returns the canonical name of a lambda
abstraction, which is based on its position in the source code. The
function \texttt{selectorId} returns the name of an auxiliary function
that is used to extract components of a pattern in a pattern
declaration (see p.~\pageref{pattern-binding} in
Sect.~\ref{sec:simplify}).
\begin{verbatim}

> module PredefIdent where
> import Ident
> import List
> import Position

> preludeMIdent, debugPreludeMIdent, ptrMIdent, stablePtrMIdent :: ModuleIdent
> preludeMIdent      = mkMIdent ["Prelude"]
> debugPreludeMIdent = mkMIdent ["DebugPrelude"]
> ptrMIdent          = mkMIdent ["Ptr"]
> stablePtrMIdent    = mkMIdent ["StablePtr"]

> lambdaId :: Position -> Ident
> lambdaId (Position _ l c) =
>   mkIdent ("_#lambda_line_" ++ show l ++ '.' : show c)

> boolId, charId, intId, floatId, ioId, successId :: Ident
> boolId    = mkIdent "Bool"
> charId    = mkIdent "Char"
> intId     = mkIdent "Int"
> floatId   = mkIdent "Float"
> ioId      = mkIdent "IO"
> successId = mkIdent "Success"

> ptrId, funPtrId, stablePtrId :: Ident
> ptrId       = mkIdent "Ptr"
> funPtrId    = mkIdent "FunPtr"
> stablePtrId = mkIdent "StablePtr"

> trueId, falseId :: Ident
> trueId  = mkIdent "True"
> falseId = mkIdent "False"

> selectorId :: Int -> Ident
> selectorId n = mkIdent ("_#sel" ++ show n)

> isSelectorId :: Ident -> Bool
> isSelectorId x = any ("_#sel" `isPrefixOf`) (tails (name x))

> mainId, minusId, fminusId :: Ident
> mainId = mkIdent "main"
> minusId = mkIdent "-"
> fminusId = mkIdent "-."

> qBoolId, qCharId, qIntId, qFloatId, qSuccessId, qIOId :: QualIdent
> qBoolId = qualifyWith preludeMIdent boolId
> qCharId = qualifyWith preludeMIdent charId
> qIntId = qualifyWith preludeMIdent intId
> qFloatId = qualifyWith preludeMIdent floatId
> qSuccessId = qualifyWith preludeMIdent successId
> qIOId = qualifyWith preludeMIdent ioId

> qPtrId, qFunPtrId, qStablePtrId :: QualIdent
> qPtrId = qualifyWith ptrMIdent ptrId
> qFunPtrId = qualifyWith ptrMIdent funPtrId
> qStablePtrId = qualifyWith stablePtrMIdent stablePtrId

> qTrueId, qFalseId :: QualIdent
> qTrueId = qualifyWith preludeMIdent trueId
> qFalseId = qualifyWith preludeMIdent falseId

> isQSelectorId :: QualIdent -> Bool
> isQSelectorId = isSelectorId . unqualify

\end{verbatim}
