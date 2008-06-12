% -*- LaTeX -*-
% $Id: IntfQual.lhs 2718 2008-06-12 14:04:58Z wlux $
%
% Copyright (c) 2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfQual.lhs}
\section{Qualification of Interface Declarations}
After applying syntax checking to an interface, the compiler properly
qualifies all unqualified identifiers in the interface in order to
simplify processing. On the other hand, the names of entities defined
in the current module are changed back into unqualified identifiers in
the final interface of the current module in order to improve
readability.

\ToDo{In order to improve readability further, remove module
  qualifiers in the right hand side of interface declarations for all
  names which are unambiguous.}
\begin{verbatim}

> module IntfQual(Qual, qualIntf,unqualIntf) where
> import Base
> import Curry
> import IdentInfo
> import PredefIdent

> qualIntf :: Qual a => ModuleIdent -> a -> a
> qualIntf = mapQId qualQualify

> unqualIntf :: Qual a => ModuleIdent -> a -> a
> unqualIntf = mapQId qualUnqualify

> class Qual a where
>   mapQId :: (ModuleIdent -> QualIdent -> QualIdent) -> ModuleIdent -> a -> a

> instance Qual a => Qual [a] where
>   mapQId q m = map (mapQId q m)

> instance Qual IDecl where
>   mapQId q m (IInfixDecl p fix pr op) = IInfixDecl p fix pr (mapDC q m op)
>   mapQId q m (HidingDataDecl p tc tvs) = HidingDataDecl p (mapTC q m tc) tvs
>   mapQId q m (IDataDecl p tc tvs cs xs) =
>     IDataDecl p (mapTC q m tc) tvs (mapQId q m cs) xs
>   mapQId q m (INewtypeDecl p tc tvs nc xs) =
>     INewtypeDecl p (mapTC q m tc) tvs (mapQId q m nc) xs
>   mapQId q m (ITypeDecl p tc tvs ty) =
>     ITypeDecl p (mapTC q m tc) tvs (mapQId q m ty)
>   mapQId q m (IFunctionDecl p f n ty) =
>     IFunctionDecl p (q m f) n (mapQId q m ty)

> instance Qual ConstrDecl where
>   mapQId q m (ConstrDecl p tvs c tys) = ConstrDecl p tvs c (mapQId q m tys)
>   mapQId q m (ConOpDecl p tvs ty1 op ty2) =
>     ConOpDecl p tvs (mapQId q m ty1) op (mapQId q m ty2)
>   mapQId q m (RecordDecl p tvs c fs) = RecordDecl p tvs c (mapQId q m fs)

> instance Qual NewConstrDecl where
>   mapQId q m (NewConstrDecl p c ty) = NewConstrDecl p c (mapQId q m ty)
>   mapQId q m (NewRecordDecl p c l ty) = NewRecordDecl p c l (mapQId q m ty)

> instance Qual FieldDecl where
>   mapQId q m (FieldDecl p ls ty) = FieldDecl p ls (mapQId q m ty)

> instance Qual TypeExpr where
>   mapQId q m (ConstructorType tc tys) =
>     ConstructorType (mapTC q m tc) (mapQId q m tys)
>   mapQId q _ (VariableType tv) = VariableType tv
>   mapQId q m (TupleType tys) = TupleType (mapQId q m tys)
>   mapQId q m (ListType ty) = ListType (mapQId q m ty)
>   mapQId q m (ArrowType ty1 ty2) = ArrowType (mapQId q m ty1) (mapQId q m ty2)

> mapTC, mapDC :: (ModuleIdent -> QualIdent -> QualIdent)
>              -> ModuleIdent -> QualIdent -> QualIdent
> mapTC = mapQIdent isPrimTypeId
> mapDC = mapQIdent isPrimDataId

> mapQIdent :: (Ident -> Bool) -> (ModuleIdent -> QualIdent -> QualIdent)
>           -> ModuleIdent -> QualIdent -> QualIdent
> mapQIdent p q m x = q (if p (unqualify x) then preludeMIdent else m) x

\end{verbatim}
