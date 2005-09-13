% -*- LaTeX -*-
% $Id: IntfCheck.lhs 1767 2005-09-13 18:39:29Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfCheck.lhs}
\section{Checking Interface Files}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler checks that the definitions of the imported
entities are compatible with their original definitions and that all
type constructor applications are saturated.

At this point, an alert reader might ask why the compiler includes
definitions in interface files that are imported from other modules.
After all, the compiler loads all of those interfaces anyway. The
answer is twofold. First, this policy ensures that an interface is
updated when the definition of an imported entity is changed, which is
exported from the module. Therefore, it is sufficient to check the
time stamps of the interface files imported directly into a module in
order to check whether the module is out of date and must be
recompiled. The second reason is that by including those definitions
in the interface, the compiler could in principle avoid loading the
imported interfaces themselves, which would save processing time and
allow building abstract packages from a set of modules. However, this
has not been implemented yet.
\begin{verbatim}

> module IntfCheck(intfCheck,fixInterface,intfEquiv) where
> import Base
> import List
> import Maybe
> import Set
> import TopEnv

> infix 4 =~=, `eqvList`, `eqvSet`

\end{verbatim}
The function \texttt{intfCheck} is the main entry point into this 
module.
\begin{verbatim}

> intfCheck :: PEnv -> TCEnv -> ValueEnv -> Interface -> Interface
> intfCheck pEnv tcEnv tyEnv (Interface m is ds) =
>   Interface m is (map (checkImport pEnv tcEnv tyEnv . checkIDecl env) ds)
>   where env = foldr (bindType m) (fmap typeKind tcEnv) ds

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in the interface.
\begin{verbatim}

> bindType :: ModuleIdent -> IDecl -> TypeEnv -> TypeEnv
> bindType m (HidingDataDecl _ tc tvs) =
>   bindTop m tc (Data (qualifyWith m tc) (length tvs) [])
> bindType m (IDataDecl _ tc tvs _) =
>   bindTopLocal m tc (Data tc (length tvs) [])
> bindType m (INewtypeDecl _ tc tvs _) =
>   bindTopLocal m tc (Data tc (length tvs) [])
> bindType m (ITypeDecl _ tc tvs ty) =
>   bindTopLocal m tc (Alias tc (length tvs))
> bindType _ _ = id

> bindTopLocal :: ModuleIdent -> QualIdent -> TypeKind -> TypeEnv -> TypeEnv
> bindTopLocal m tc x =
>   case splitQualIdent tc of
>     (Just _,_) -> id
>     (Nothing,tc') -> bindTop m tc' x

\end{verbatim}
The checks applied to the interface are similar to those performed
during syntax checking of type expressions. However, there are no
nested declarations. In addition, synonym types must not occur in type
expressions.
\begin{verbatim}

> checkIDecl :: TypeEnv -> IDecl -> IDecl
> checkIDecl env (HidingDataDecl p tc tvs) =
>   HidingDataDecl p tc (checkTypeLhs env p tvs)
> checkIDecl env (IDataDecl p tc tvs cs) =
>   IDataDecl p tc tvs' (map (fmap (checkConstrDecl env tvs')) cs)
>   where tvs' = checkTypeLhs env p tvs
> checkIDecl env (INewtypeDecl p tc tvs nc) =
>   INewtypeDecl p tc tvs' (checkNewConstrDecl env tvs' nc)
>   where tvs' = checkTypeLhs env p tvs
> checkIDecl env (ITypeDecl p tc tvs ty) =
>   ITypeDecl p tc tvs' (checkClosedType env p tvs' ty)
>   where tvs' = checkTypeLhs env p tvs
> checkIDecl env (IFunctionDecl p f ty) =
>   IFunctionDecl p f (checkType env p ty)
> checkIDecl _ d = d

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> [Ident]
> checkTypeLhs env p (tv:tvs)
>   | isTypeConstr tv = errorAt p (noVariable tv)
>   | tv `elem` tvs = errorAt p  (nonLinear tv)
>   | otherwise = tv : checkTypeLhs env p tvs
>   where isTypeConstr tv = not (null (lookupType tv env))
> checkTypeLhs env p [] = []

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs' c (map (checkClosedType env p tvs') tys)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs' (checkClosedType env p tvs' ty1) op
>             (checkClosedType env p tvs' ty2)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl -> NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs' c (checkClosedType env p tvs' ty)
>   where evs' = checkTypeLhs env p evs
>         tvs' = evs' ++ tvs

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosedType env p tvs ty = checkClosed p tvs (checkType env p ty)

> checkType :: TypeEnv -> Position -> TypeExpr -> TypeExpr
> checkType env p (ConstructorType tc tys) =
>   case qualLookupType tc env of
>     []
>       | not (isQualified tc) && null tys -> VariableType (unqualify tc)
>       | otherwise -> errorAt p (undefinedType tc)
>     [Data tc' n _]
>       | n == n' -> ConstructorType tc' (map (checkType env p) tys)
>       | otherwise -> errorAt p (wrongArity tc n n')
>       where n' = length tys
>     [Alias _ _] -> errorAt p (badTypeSynonym tc)
>     _ -> internalError "checkType"
> checkType env p (VariableType tv) =
>   checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) = TupleType (map (checkType env p) tys)
> checkType env p (ListType ty) = ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   ArrowType (checkType env p ty1) (checkType env p ty2)

> checkClosed :: Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosed p tvs (ConstructorType tc tys) =
>   ConstructorType tc (map (checkClosed p tvs) tys)
> checkClosed p tvs (VariableType tv)
>   | tv `notElem` tvs = errorAt p (unboundVariable tv)
>   | otherwise = VariableType tv
> checkClosed p tvs (TupleType tys) =
>   TupleType (map (checkClosed p tvs) tys)
> checkClosed p tvs (ListType ty) =
>   ListType (checkClosed p tvs ty)
> checkClosed p tvs (ArrowType ty1 ty2) =
>   ArrowType (checkClosed p tvs ty1) (checkClosed p tvs ty2)

\end{verbatim}
\ToDo{Define the above code in module \texttt{TypeSyntaxCheck} in
  order to share as much code as possible.}

After checking the declarations, the compiler asserts that all
imported definitions actually match their original definition. This is
necessary in order to detect inconsistent interfaces.
\begin{verbatim}

> checkImport :: PEnv -> TCEnv -> ValueEnv -> IDecl -> IDecl
> checkImport pEnv _ _ (IInfixDecl p fix pr op) =
>   case splitQualIdent op of
>     (Just m,op') ->
>       case qualLookupP op pEnv of
>         [] -> errorAt p (noPrecedence m op')
>         [PrecInfo op'' (OpPrec fix' pr')]
>           | op == op'' && fix == fix' && pr == pr' -> IInfixDecl p fix pr op
>           | otherwise -> errorAt p (importConflict "precedence" m op')
>         _ -> internalError "checkImport (IInfixDecl)"
>     (Nothing,_) -> IInfixDecl p fix pr op
> checkImport _ _ _ (HidingDataDecl p tc tvs) = HidingDataDecl p tc tvs
> checkImport _ tcEnv tyEnv (IDataDecl p tc tvs cs) =
>   case splitQualIdent tc of
>     (Just m,tc') ->
>       case qualLookupTC tc tcEnv of
>         [] -> errorAt p (notExported "data type" m tc')
>         [DataType tc'' n' cs']
>           | tc == tc'' && length tvs == n' &&
>             (null cs || length cs == length cs') &&
>             and (zipWith isVisible cs cs') ->
>               IDataDecl p tc tvs
>                         (map (fmap (checkConstrImport m tyEnv tvs)) cs)
>           where isVisible (Just c) (Just c') = constr c == c'
>                 isVisible (Just _) Nothing = False
>                 isVisible Nothing _ = True
>         [RenamingType tc'' n' _]
>           | tc == tc'' && length tvs == n' && null cs -> IDataDecl p tc tvs []
>         [_] -> errorAt p (importConflict "data type" m tc')
>         _ -> internalError "checkImport (IDataDecl)"
>     (Nothing,_) -> IDataDecl p tc tvs cs
> checkImport _ tcEnv tyEnv (INewtypeDecl p tc tvs nc) =
>   case splitQualIdent tc of
>     (Just m,tc') ->
>       case qualLookupTC tc tcEnv of
>         [] -> errorAt p (notExported "newtype" m tc')
>         [RenamingType tc'' n' nc']
>           | tc == tc'' && length tvs == n' && nconstr nc == nc' ->
>               INewtypeDecl p tc tvs (checkNewConstrImport m tyEnv tvs nc)
>         [_] -> errorAt p (importConflict "newtype" m tc')
>         _ -> internalError "checkImport (INewtypeDecl)"
>     (Nothing,_) -> INewtypeDecl p tc tvs nc
> checkImport _ tcEnv _ (ITypeDecl p tc tvs ty) =
>   case splitQualIdent tc of
>     (Just m,tc') -> 
>       case qualLookupTC tc tcEnv of
>         [] -> errorAt p (notExported "synonym type" m tc')
>         [AliasType tc'' n' ty']
>           | tc == tc'' && length tvs == n' && toQualType m tvs ty == ty' ->
>               ITypeDecl p tc tvs ty
>         [_] -> errorAt p (importConflict "synonym type" m tc')
>         _ -> internalError "checkImport (ITypeDecl)"
>     (Nothing,_) -> ITypeDecl p tc tvs ty
> checkImport _ _ tyEnv (IFunctionDecl p f ty) =
>   case splitQualIdent f of
>     (Just m,f') ->
>       case qualLookupValue f tyEnv of
>         [] -> errorAt p (notExported "function" m f')
>         [Value f'' (ForAll _ ty')]
>           | f == f'' && toQualType m [] ty == ty' -> IFunctionDecl p f ty
>         [_] -> errorAt p (importConflict "function" m f')
>         _ -> internalError "checkImport (IFunctionDecl)"
>     (Nothing,_) -> IFunctionDecl p f ty

> checkConstrImport :: ModuleIdent -> ValueEnv -> [Ident] -> ConstrDecl
>                   -> ConstrDecl
> checkConstrImport m tyEnv tvs (ConstrDecl p evs c tys) =
>   case qualLookupValue qc tyEnv of
>     [DataConstructor c' (ForAllExist _ n' ty')]
>       | qc == c' && length evs == n' &&
>         toQualTypes m tvs tys == arrowArgs ty' ->
>           ConstrDecl p evs c tys
>       | otherwise -> errorAt p (importConflict "data constructor" m c)
>     _ -> internalError "checkConstrImport"
>   where qc = qualifyWith m c
> checkConstrImport m tyEnv tvs (ConOpDecl p evs ty1 op ty2) =
>   case qualLookupValue qc tyEnv of
>     [DataConstructor c' (ForAllExist _ n' ty')]
>       | qc == c' && length evs == n' &&
>         toQualTypes m tvs [ty1,ty2] == arrowArgs ty' ->
>           ConOpDecl p evs ty1 op ty2
>       | otherwise -> errorAt p (importConflict "data constructor" m op)
>     _ -> internalError "checkConstrImport"
>   where qc = qualifyWith m op

> checkNewConstrImport :: ModuleIdent -> ValueEnv -> [Ident] -> NewConstrDecl
>                      -> NewConstrDecl
> checkNewConstrImport m tyEnv tvs (NewConstrDecl p evs c ty) =
>   case qualLookupValue qc tyEnv of
>     [NewtypeConstructor c' (ForAllExist _ n' ty')]
>       | qc == c' && length evs == n' &&
>         toQualType m tvs ty == head (arrowArgs ty') ->
>           NewConstrDecl p evs c ty
>       | otherwise -> errorAt p (importConflict "newtype constructor" m c)
>     _ -> internalError "checkNewConstrImport"
>   where qc = qualifyWith m c

\end{verbatim}
If a module is recompiled, the compiler has to check whether the
interface file must be updated. This must be done if any exported
entity has been changed, or an export was removed or added. The
function \texttt{intfEquiv} checks whether two interfaces are
equivalent, i.e., whether they define the same entities.

\textbf{Note:} There is deliberately no list instance for
\texttt{IntfEquiv} because the order of interface declarations is
irrelevant, whereas it is decisive for the constructor declarations
of a data type. By not providing a list instance, we cannot
inadvertently mix up these cases.
\begin{verbatim}

> intfEquiv :: Interface -> Interface -> Bool
> intfEquiv = (=~=)

> class IntfEquiv a where
>   (=~=) :: a -> a -> Bool

> eqvList, eqvSet :: IntfEquiv a => [a] -> [a] -> Bool
> xs `eqvList` ys = length xs == length ys && and (zipWith (=~=) xs ys)
> xs `eqvSet` ys =
>   null (deleteFirstsBy (=~=) xs ys ++ deleteFirstsBy (=~=) ys xs)

> instance IntfEquiv a => IntfEquiv (Maybe a) where
>   Nothing =~= Nothing = True
>   Nothing =~= Just _  = False
>   Just _  =~= Nothing = False
>   Just x  =~= Just y  = x =~= y

> instance IntfEquiv Interface where
>   Interface m1 is1 ds1 =~= Interface m2 is2 ds2 =
>     m1 == m2 && is1 `eqvSet` is2 && ds1 `eqvSet` ds2

> instance IntfEquiv IImportDecl where
>   IImportDecl _ m1 =~= IImportDecl _ m2 = m1 == m2

> instance IntfEquiv IDecl where
>   IInfixDecl _ fix1 p1 op1 =~= IInfixDecl _ fix2 p2 op2 =
>     fix1 == fix2 && p1 == p2 && op1 == op2
>   HidingDataDecl _ tc1 tvs1 =~= HidingDataDecl _ tc2 tvs2 =
>     tc1 == tc2 && tvs1 == tvs2
>   IDataDecl _ tc1 tvs1 cs1 =~= IDataDecl _ tc2 tvs2 cs2 =
>     tc1 == tc2 && tvs1 == tvs2 && cs1 `eqvList` cs2
>   INewtypeDecl _ tc1 tvs1 nc1 =~= INewtypeDecl _ tc2 tvs2 nc2 =
>     tc1 == tc2 && tvs1 == tvs2 && nc1 =~= nc2
>   ITypeDecl _ tc1 tvs1 ty1 =~= ITypeDecl _ tc2 tvs2 ty2 = 
>     tc1 == tc2 && tvs1 == tvs2 && ty1 == ty2
>   IFunctionDecl _ f1 ty1 =~= IFunctionDecl _ f2 ty2 = f1 == f2 && ty1 == ty2
>   _ =~= _ = False

> instance IntfEquiv ConstrDecl where
>   ConstrDecl _ evs1 c1 tys1 =~= ConstrDecl _ evs2 c2 tys2 =
>     c1 == c2 && evs1 == evs2 && tys1 == tys2
>   ConOpDecl _ evs1 ty11 op1 ty12 =~= ConOpDecl _ evs2 ty21 op2 ty22 =
>     op1 == op2 && evs1 == evs2 && ty11 == ty21 && ty12 == ty22
>   _ =~= _ = False

> instance IntfEquiv NewConstrDecl where
>   NewConstrDecl _ evs1 c1 ty1 =~= NewConstrDecl _ evs2 c2 ty2 =
>     c1 == c2 && evs1 == evs2 && ty1 == ty2

\end{verbatim}
If we check for a change in the interface, we do not need to check the
interface declarations, but still must disambiguate (nullary) type
constructors and type variables in type expressions. This is handled
by the function \texttt{fixInterface} and the associated type class
\texttt{FixInterface}.
\begin{verbatim}

> fixInterface :: Interface -> Interface
> fixInterface (Interface m is ds) =
>   Interface m is (fix (fromListSet (typeConstructors ds)) ds)

> class FixInterface a where
>   fix :: Set Ident -> a -> a

> instance FixInterface a => FixInterface (Maybe a) where
>   fix tcs = fmap (fix tcs)

> instance FixInterface a => FixInterface [a] where
>   fix tcs = map (fix tcs)

> instance FixInterface IDecl where
>   fix tcs (IDataDecl p tc tvs cs) = IDataDecl p tc tvs (fix tcs cs)
>   fix tcs (INewtypeDecl p tc tvs nc) = INewtypeDecl p tc tvs (fix tcs nc)
>   fix tcs (ITypeDecl p tc tvs ty) = ITypeDecl p tc tvs (fix tcs ty)
>   fix tcs (IFunctionDecl p f ty) = IFunctionDecl p f (fix tcs ty)
>   fix _ d = d

> instance FixInterface ConstrDecl where
>   fix tcs (ConstrDecl p evs c tys) = ConstrDecl p evs c (fix tcs tys)
>   fix tcs (ConOpDecl p evs ty1 op ty2) =
>     ConOpDecl p evs (fix tcs ty1) op (fix tcs ty2)

> instance FixInterface NewConstrDecl where
>   fix tcs (NewConstrDecl p evs c ty) = NewConstrDecl p evs c (fix tcs ty)

> instance FixInterface TypeExpr where
>   fix tcs (ConstructorType tc tys)
>     | not (isQualified tc) && tc' `notElemSet` tcs && null tys =
>         VariableType tc'
>     | otherwise = ConstructorType tc (fix tcs tys)
>     where tc' = unqualify tc
>   fix tcs (VariableType tv)
>     | tv `elemSet` tcs = ConstructorType (qualify tv) []
>     | otherwise = VariableType tv
>   fix tcs (TupleType tys) = TupleType (fix tcs tys)
>   fix tcs (ListType ty) = ListType (fix tcs ty)
>   fix tcs (ArrowType ty1 ty2) = ArrowType (fix tcs ty1) (fix tcs ty2)

> typeConstructors :: [IDecl] -> [Ident]
> typeConstructors = foldr tcs []
>   where tcs (HidingDataDecl _ tc _) tcs = tc : tcs
>         tcs (IDataDecl _ tc _ _) tcs = localTC tc tcs
>         tcs (INewtypeDecl _ tc _ _) tcs = localTC tc tcs
>         tcs (ITypeDecl _ tc _ _) tcs = localTC tc tcs
>         tcs _ tcs = tcs
>         localTC tc = maybe (tc' :) (const id) m'
>           where (m',tc') = splitQualIdent tc

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type constructor " ++ qualName tc

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noVariable :: Ident -> String
> noVariable tv =
>   "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity tc arity argc =
>   "Type constructor " ++ qualName tc ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> unboundVariable :: Ident -> String
> unboundVariable tv = "Unbound type variable " ++ name tv

> badTypeSynonym :: QualIdent -> String
> badTypeSynonym tc = "Synonym type " ++ qualName tc ++ " in interface"

> notExported :: String -> ModuleIdent -> Ident -> String
> notExported what m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not export " ++ what ++ " " ++ name x

> noPrecedence :: ModuleIdent -> Ident -> String
> noPrecedence m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not define a precedence for " ++ name x

> importConflict :: String -> ModuleIdent -> Ident -> String
> importConflict what m x =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of " ++ what ++ " " ++ name x ++
>   " does not match its definition in module " ++ moduleName m

\end{verbatim}
