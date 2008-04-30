% -*- LaTeX -*-
% $Id: PredefTypes.lhs 2686 2008-04-30 19:30:57Z wlux $
%
% Copyright (c) 2002-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PredefTypes.lhs}
\section{Predefined Types}
This module defines the predefined types that are known to the
compiler.
\begin{verbatim}

> module PredefTypes where
> import Ident
> import PredefIdent
> import Types

> unitType,boolType,charType,intType,floatType,stringType,successType :: Type
> unitType = TypeConstructor qUnitId []
> boolType = TypeConstructor qBoolId []
> charType = TypeConstructor qCharId []
> intType = TypeConstructor qIntId []
> floatType = TypeConstructor qFloatId []
> stringType = listType charType
> successType = TypeConstructor qSuccessId []

> listType,ioType :: Type -> Type
> listType ty = TypeConstructor qListId [ty]
> ioType ty = TypeConstructor qIOId [ty]

> tupleType :: [Type] -> Type
> tupleType tys = TypeConstructor (qTupleId (length tys)) tys

\end{verbatim}
The unit, list, and tuple types are predefined and available in every
module.
\begin{verbatim}

> predefTypes :: [(Type,[(QualIdent,Type)])]
> predefTypes =
>   let a = TypeVariable 0 in [
>     (unitType,   [(qUnitId,unitType)]),
>     (listType a, [(qNilId,nilType a), (qConsId,consType a)])
>   ]
>   where nilType a = listType a
>         consType a = TypeArrow a (TypeArrow (listType a) (listType a))

> tupleTypes :: [Type]
> tupleTypes = [tupleType (take n tvs) | n <- [2..]]
>   where tvs = map TypeVariable [0..]

\end{verbatim}
