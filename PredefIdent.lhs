% -*- LaTeX -*-
% $Id: PredefIdent.lhs 2686 2008-04-30 19:30:57Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
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

> unitId, nilId, consId, listId :: Ident
> unitId = mkIdent "()"
> nilId  = mkIdent "[]"
> consId = mkIdent ":"
> listId = mkIdent "[]"

> tupleId :: Int -> Ident
> tupleId n
>   | n >= 2 = mkIdent ("(" ++ replicate (n - 1) ',' ++ ")")
>   | otherwise = error "internal error: tupleId"

> isTupleId :: Ident -> Bool
> isTupleId x = n > 1 && x == tupleId n
>   where n = length (name x) - 1

> tupleArity :: Ident -> Int
> tupleArity x
>   | n > 1 && x == tupleId n = n
>   | otherwise = error "internal error: tupleArity"
>   where n = length (name x) - 1

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

> qUnitId, qNilId, qConsId, qListId :: QualIdent
> qUnitId = qualifyWith preludeMIdent unitId
> qNilId  = qualifyWith preludeMIdent nilId
> qConsId = qualifyWith preludeMIdent consId
> qListId = qualifyWith preludeMIdent listId

> qTupleId :: Int -> QualIdent
> qTupleId = qualifyWith preludeMIdent . tupleId

> isQTupleId :: QualIdent -> Bool
> isQTupleId = isTupleId . unqualify

> qTupleArity :: QualIdent -> Int
> qTupleArity = tupleArity . unqualify

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
The type and data constructors of the unit, list, and tuple types are
handled specially. Conceptually, these entities belong to the Prelude
but they can be accessed only with special syntax and cannot be
defined by the user. Furthermore, these entities are available in
every module. The functions \texttt{isPrimTypeId} and
\texttt{isPrimDataId} can be used to check for the type and data
constructor identifiers of these types.
\begin{verbatim}

> isPrimTypeId :: QualIdent -> Bool
> isPrimTypeId tc = tc' `elem` [unitId,listId] || isTupleId tc'
>   where tc' = unqualify tc

> isPrimDataId :: QualIdent -> Bool
> isPrimDataId c = c' `elem` [unitId,nilId,consId] || isTupleId c'
>   where c' = unqualify c

\end{verbatim}
