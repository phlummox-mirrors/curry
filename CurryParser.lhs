% -*- LaTeX -*-
% $Id: CurryParser.lhs 2677 2008-04-22 14:42:42Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryParser.lhs}
\section{A Parser for Curry}
The Curry parser is implemented using the (mostly) LL(1) parsing
combinators described in appendix~\ref{sec:ll-parsecomb}.
\begin{verbatim}

> module CurryParser(parseSource, parseHeader, parseInterface, parseGoal) where
> import Error
> import LexComb
> import LLParseComb
> import Curry
> import CurryLexer
> import PathUtils
> import PredefIdent

> instance Symbol Token where
>   isEOF (Token c _) = c == EOF

\end{verbatim}
\paragraph{Modules}
\begin{verbatim}

> parseSource :: FilePath -> String -> Error (Module ())
> parseSource fn = applyParser (parseModule fn) lexer fn

> parseHeader :: FilePath -> String -> Error (Module ())
> parseHeader fn = prefixParser (moduleHeader fn <*->
>                                (leftBrace <|> layoutOn) <*>
>                                importDecls <*>
>                                succeed [])
>                               lexer
>                               fn
>   where importDecls = (:) <$> importDecl <*> importDecls' `opt` []
>         importDecls' = semicolon <-*> importDecls `opt` []

> parseModule :: FilePath -> Parser Token (Module ()) a
> parseModule fn = uncurry <$> moduleHeader fn <*> layout moduleDecls

> moduleHeader :: FilePath
>              -> Parser Token ([ImportDecl] -> [TopDecl ()] -> Module ()) a
> moduleHeader fn = Module <$-> token KW_module
>                          <*> (mIdent <?> "module name expected")
>                          <*> option exportSpec
>                          <*-> (token KW_where <?> "where expected")
>             `opt` Module (defaultMIdent fn) Nothing

> exportSpec :: Parser Token ExportSpec a
> exportSpec = Exporting <$> position <*> parens (export `sepBy` comma)

> export :: Parser Token Export a
> export = qtycon <**> (parens spec `opt` Export)
>      <|> Export <$> qfun <\> qtycon
>      <|> ExportModule <$-> token KW_module <*> mIdent
>   where spec = ExportTypeAll <$-> token DotDot
>            <|> flip ExportTypeWith <$> con `sepBy` comma

> moduleDecls :: Parser Token ([ImportDecl],[TopDecl ()]) a
> moduleDecls = imp <$> importDecl <?*> semiBlock moduleDecls ([],[])
>           <|> top <$> topDecl <*> semiBlock (block topDecl) []
>   where imp i ~(is,ds) = (i:is,ds)
>         top d ds = ([],d:ds)

> importDecl :: Parser Token ImportDecl a
> importDecl =
>   flip . ImportDecl <$> position <*-> token KW_import 
>                     <*> flag (token Id_qualified)
>                     <*> mIdent
>                     <*> option (token Id_as <-*> mIdent)
>                     <*> option importSpec

> importSpec :: Parser Token ImportSpec a
> importSpec = position <**> (Hiding <$-> token Id_hiding `opt` Importing)
>                       <*> parens (spec `sepBy` comma)
>   where spec = tycon <**> (parens constrs `opt` Import)
>            <|> Import <$> fun <\> tycon
>         constrs = ImportTypeAll <$-> token DotDot
>               <|> flip ImportTypeWith <$> con `sepBy` comma

\end{verbatim}
If a source module has no explicit module header, the compiler
substitutes a default module header \texttt{module} $M$
\texttt{where} if the module is saved in file $M$\texttt{.curry}. The
directory path to the module is ignored.
\begin{verbatim}

> defaultMIdent :: FilePath -> ModuleIdent
> defaultMIdent fn = mkMIdent [rootname (basename fn)]

\end{verbatim}
\paragraph{Interfaces}
\begin{verbatim}

> parseInterface :: FilePath -> String -> Error Interface
> parseInterface fn s = applyParser parseIntf lexer fn s

> parseIntf :: Parser Token Interface a
> parseIntf = uncurry <$> intfHeader <*> braces intfDecls

> intfHeader :: Parser Token ([IImportDecl] -> [IDecl] -> Interface) a
> intfHeader = Interface <$-> token Id_interface <*> moduleName
>                        <*-> (token KW_where <?> "where expected")
>   where moduleName = mIdent
>                  <|> mkMIdent . return <$> string
>                  <?> "module name expected"

> intfDecls :: Parser Token ([IImportDecl],[IDecl]) a
> intfDecls = imp <$> iImportDecl <?*> semiBlock intfDecls ([],[])
>         <|> intf <$> intfDecl <*> semiBlock (block intfDecl) []
>   where imp i ~(is,ds) = (i:is,ds)
>         intf d ds = ([],d:ds)

> iImportDecl :: Parser Token IImportDecl a
> iImportDecl = IImportDecl <$> position <*-> token KW_import <*> mIdent

\end{verbatim}
\paragraph{Goals}
\begin{verbatim}

> parseGoal :: String -> Error (Goal ())
> parseGoal s = applyParser goal lexer "" s

> goal :: Parser Token (Goal ()) a
> goal = Goal <$> position <*> expr <*> whereClause

\end{verbatim}
\paragraph{Declarations}
\begin{verbatim}

> topDecl :: Parser Token (TopDecl ()) a
> topDecl = dataDecl <|> newtypeDecl <|> typeDecl <|> BlockDecl <$> blockDecl
>   where blockDecl = infixDecl <|> functionDecl <|> foreignDecl
>                 <|> trustAnnotation

> whereClause :: Parser Token [Decl ()] a
> whereClause = token KW_where <-*> localDecls
>         `opt` []

> localDecls :: Parser Token [Decl ()] a
> localDecls = layout (block localDecl)

> localDecl :: Parser Token (Decl ()) a
> localDecl = infixDecl <|> valueDecl <|> foreignDecl <|> trustAnnotation

> dataDecl :: Parser Token (TopDecl ()) a
> dataDecl = typeDeclLhs DataDecl KW_data <*> constrs
>   where constrs = equals <-*> constrDecl `sepBy1` bar
>             `opt` []

> newtypeDecl :: Parser Token (TopDecl ()) a
> newtypeDecl = typeDeclLhs NewtypeDecl KW_newtype <*-> equals <*> newConstrDecl

> typeDecl :: Parser Token (TopDecl ()) a
> typeDecl = typeDeclLhs TypeDecl KW_type <*-> equals <*> type0

> typeDeclLhs :: (Position -> Ident -> [Ident] -> a) -> Category
>             -> Parser Token a b
> typeDeclLhs f kw = f <$> position <*-> token kw <*> tycon <*> many typeVar
>   where typeVar = tyvar <|> anonId <$-> token Underscore

> constrDecl :: Parser Token ConstrDecl a
> constrDecl = position <**> (existVars <**> constr)
>   where existVars = token Id_forall <-*> many1 tyvar <*-> dot `opt` []
>         constr = conId <**> identDecl
>              <|> leftParen <-*> parenDecl
>              <|> type1 <\> conId <\> leftParen <**> opDecl
>         identDecl = many type2 <**> (conType <$> opDecl `opt` conDecl)
>                 <|> recDecl <$> fields
>         parenDecl = conSym <*-> rightParen <**> opSymDecl
>                 <|> tupleType <*-> rightParen <**> opDecl
>         opSymDecl = conDecl <$> many type2
>                 <|> recDecl <$> fields
>         opDecl = conOpDecl <$> conop <*> type1
>         fields = braces (fieldDecl `sepBy` comma)
>         conType f tys c = f (ConstructorType (qualify c) tys)
>         conDecl tys c tvs p = ConstrDecl p tvs c tys
>         conOpDecl op ty2 ty1 tvs p = ConOpDecl p tvs ty1 op ty2
>         recDecl fs c tvs p = RecordDecl p tvs c fs

> fieldDecl :: Parser Token FieldDecl a
> fieldDecl = FieldDecl <$> position <*> labels <*-> token DoubleColon <*> type0
>   where labels = fun `sepBy1` comma

> newConstrDecl :: Parser Token NewConstrDecl a
> newConstrDecl = position <**> (con <**> newConstr)
>   where newConstr = newConDecl <$> type2
>                 <|> newRecDecl <$> braces newFieldDecl
>         newConDecl ty c p = NewConstrDecl p c ty
>         newRecDecl (l,ty) c p = NewRecordDecl p c l ty

> newFieldDecl :: Parser Token (Ident,TypeExpr) a
> newFieldDecl = (,) <$> fun <*-> token DoubleColon <*> type0

> infixDecl :: Parser Token (Decl ()) a
> infixDecl = infixDeclLhs InfixDecl <*> option int <*> funop `sepBy1` comma

> infixDeclLhs :: (Position -> Infix -> a) -> Parser Token a b
> infixDeclLhs f = f <$> position <*> tokenOps infixKW
>   where infixKW = [(KW_infix,Infix),(KW_infixl,InfixL),(KW_infixr,InfixR)]

> functionDecl :: Parser Token (Decl ()) a
> functionDecl = position <**> decl
>   where decl = fun `sepBy1` comma <**> funListDecl
>           <|?> funDecl <$> lhs <*> declRhs
>         lhs = (\f -> (f,FunLhs f [])) <$> fun
>          <|?> funLhs

> valueDecl :: Parser Token (Decl ()) a
> valueDecl = position <**> decl
>   where decl = var `sepBy1` comma <**> valListDecl
>           <|?> valDecl <$> constrTerm0 <*> declRhs
>           <|?> funDecl <$> curriedLhs <*> declRhs
>         valDecl (ConstructorPattern _ c ts)
>           | not (isConstrId c) = funDecl (f,FunLhs f ts)
>           where f = unqualify c
>         valDecl t = opDecl id t
>         opDecl f (InfixPattern a t1 op t2)
>           | isConstrId op = opDecl (f . InfixPattern a t1 op) t2
>           | otherwise = funDecl (op',OpLhs (f t1) op' t2)
>           where op' = unqualify op
>         opDecl f t = patDecl (f t)
>         isConstrId c = c == qConsId || isQualified c || isQTupleId c

> funDecl :: (Ident,Lhs a) -> Rhs a -> Position -> Decl a
> funDecl (f,lhs) rhs p = FunctionDecl p f [Equation p lhs rhs]

> patDecl :: ConstrTerm a -> Rhs a -> Position -> Decl a
> patDecl t rhs p = PatternDecl p t rhs

> funListDecl :: Parser Token ([Ident] -> Position -> Decl ()) a
> funListDecl = typeSig <$-> token DoubleColon <*> type0
>   where typeSig ty vs p = TypeSig p vs ty

> valListDecl :: Parser Token ([Ident] -> Position -> Decl ()) a
> valListDecl = funListDecl
>           <|> flip FreeDecl <$-> token KW_free

> funLhs :: Parser Token (Ident,Lhs ()) a
> funLhs = funLhs <$> fun <*> many1 constrTerm2
>     <|?> flip ($ id) <$> constrTerm1 <*> opLhs'
>     <|?> curriedLhs
>   where opLhs' = opLhs <$> funSym <*> constrTerm0
>              <|> infixPat <$> gConSym <\> funSym <*> constrTerm1 <*> opLhs'
>              <|> backquote <-*> opIdLhs
>         opIdLhs = opLhs <$> funId <*-> checkBackquote <*> constrTerm0
>               <|> infixPat <$> qConId <\> funId <*-> backquote <*> constrTerm1
>                            <*> opLhs'
>         funLhs f ts = (f,FunLhs f ts)
>         opLhs op t2 f t1 = (op,OpLhs (f t1) op t2)
>         infixPat op t2 f g t1 = f (g . InfixPattern () t1 op) t2

> curriedLhs :: Parser Token (Ident,Lhs ()) a
> curriedLhs = apLhs <$> parens funLhs <*> many1 constrTerm2
>   where apLhs (f,lhs) ts = (f,ApLhs lhs ts)

> declRhs :: Parser Token (Rhs ()) a
> declRhs = rhs equals

> rhs :: Parser Token a b -> Parser Token (Rhs ()) b
> rhs eq = rhsExpr <*> whereClause
>   where rhsExpr = SimpleRhs <$-> eq <*> position <*> expr
>               <|> GuardedRhs <$> many1 (condExpr eq)

> foreignDecl :: Parser Token (Decl ()) a
> foreignDecl =
>   mkDecl <$> position <*-> token KW_foreign <*-> token KW_import
>          <*> callConv <*> entitySpec <*-> token DoubleColon <*> type0
>   where mkDecl p cc (s,ie,f) ty = ForeignDecl p cc s ie f ty
>         callConv = CallConvPrimitive <$-> token Id_primitive
>                <|> CallConvCCall <$-> token Id_ccall
>                <|> CallConvRawCall <$-> token Id_rawcall
>         entitySpec = withSafety <$> safety <*> option importSpec
>                  <|> withoutSafety <$> importSpec <\> safety
>         safety = (,) Unsafe <$> token Id_unsafe
>              <|> (,) Safe <$> token Id_safe
>         importSpec = (,) <$> option string <*> fun
>         withSafety s (Just (ie,f)) = (Just (fst s),ie,f)
>         withSafety s Nothing =  (Nothing,Nothing,mkIdent (sval (snd s)))
>         withoutSafety (ie,f) = (Nothing,ie,f)

> trustAnnotation :: Parser Token (Decl ()) a
> trustAnnotation =
>   TrustAnnot <$> position <*> tokenOps pragmaKW <*> funList
>              <*-> token PragmaEnd
>   where pragmaKW = [(PragmaBegin SuspectPragma,Suspect),
>                     (PragmaBegin TrustPragma,Trust)]
>         funList = fun `sepBy` comma
>               <|> [] <$-> token Underscore            -- backward compability

\end{verbatim}
\paragraph{Interface declarations}
\begin{verbatim}

> intfDecl :: Parser Token IDecl a
> intfDecl = iInfixDecl
>        <|> hidingDataDecl <|> iDataDecl <|> iNewtypeDecl <|> iTypeDecl
>        <|> iFunctionDecl

> iInfixDecl :: Parser Token IDecl a
> iInfixDecl = infixDeclLhs IInfixDecl <*> int <*> qfunop

> hidingDataDecl :: Parser Token IDecl a
> hidingDataDecl =
>   position <**> pragma DataPragma (dataDecl <$> qtycon <*> many tyvar)
>   where dataDecl tc tvs p = HidingDataDecl p tc tvs

> iDataDecl :: Parser Token IDecl a
> iDataDecl = iTypeDeclLhs IDataDecl KW_data <*> constrs <*> iHidden
>   where constrs = equals <-*> constrDecl `sepBy1` bar
>             `opt` []

> iNewtypeDecl :: Parser Token IDecl a
> iNewtypeDecl =
>   iTypeDeclLhs INewtypeDecl KW_newtype <*-> equals <*> newConstrDecl
>                                        <*> iHidden

> iTypeDecl :: Parser Token IDecl a
> iTypeDecl = iTypeDeclLhs ITypeDecl KW_type <*-> equals <*> type0

> iTypeDeclLhs :: (Position -> QualIdent -> [Ident] -> a) -> Category
>              -> Parser Token a b
> iTypeDeclLhs f kw = f <$> position <*-> token kw <*> qtycon <*> many tyvar

> iHidden :: Parser Token [Ident] a
> iHidden = pragma HidingPragma (con `sepBy` comma)
>     `opt` []

> iFunctionDecl :: Parser Token IDecl a
> iFunctionDecl =
>   IFunctionDecl <$> position <*> qfun <*-> token DoubleColon
>                 <*> option iFunctionArity <*> type0

> iFunctionArity :: Parser Token Integer a
> iFunctionArity = pragma ArityPragma int

> pragma :: Pragma -> Parser Token a b -> Parser Token a b
> pragma kw p = token (PragmaBegin kw) <-*> p <*-> token PragmaEnd

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> type0 :: Parser Token TypeExpr a
> type0 = type1 `chainr1` (ArrowType <$-> token RightArrow)

> type1 :: Parser Token TypeExpr a
> type1 = ConstructorType <$> qtycon <*> many type2
>     <|> type2 <\> qtycon

> type2 :: Parser Token TypeExpr a
> type2 = anonType <|> identType <|> parenType <|> listType

> anonType :: Parser Token TypeExpr a
> anonType = VariableType anonId <$-> token Underscore

> identType :: Parser Token TypeExpr a
> identType = VariableType <$> tyvar
>         <|> flip ConstructorType [] <$> qtycon <\> tyvar

> parenType :: Parser Token TypeExpr a
> parenType = parens tupleType

> tupleType :: Parser Token TypeExpr a
> tupleType = type0 <**?> (tuple <$> many1 (comma <-*> type0))
>       `opt` ConstructorType qUnitId []
>   where tuple tys ty = TupleType (ty:tys)

> listType :: Parser Token TypeExpr a
> listType = ListType <$> brackets type0

\end{verbatim}
\paragraph{Literals}
\begin{verbatim}

> literal :: Parser Token Literal a
> literal = Char <$> char
>       <|> Int <$> int
>       <|> Float <$> float
>       <|> String <$> string

\end{verbatim}
\paragraph{Patterns}
\begin{verbatim}

> constrTerm0 :: Parser Token (ConstrTerm ()) a
> constrTerm0 = constrTerm1 `chainr1` (infixPat <$> gconop)
>   where infixPat op t1 t2 = InfixPattern () t1 op t2

> constrTerm1 :: Parser Token (ConstrTerm ()) a
> constrTerm1 = varId <**> identPattern
>           <|> qConId <\> varId <**> constrPattern
>           <|> minus <**> negNum
>           <|> fminus <**> negFloat
>           <|> leftParen <-*> parenPattern
>           <|> constrTerm2 <\> qConId <\> leftParen
>   where identPattern = optAsPattern
>                    <|> conPattern qualify <$> many1 constrTerm2
>         constrPattern = conPattern id <$> many1 constrTerm2
>                     <|> optRecPattern
>         parenPattern = minus <**> minusPattern negNum
>                    <|> fminus <**> minusPattern negFloat
>                    <|> funSym <\> minus <\> fminus <*-> rightParen
>                                                    <**> identPattern
>                    <|> gconSym <\> funSym <*-> rightParen <**> constrPattern
>                    <|> parenTuplePattern <\> minus <\> fminus <*-> rightParen
>         minusPattern p = rightParen <-*> identPattern
>                      <|> parenMinusPattern p <*-> rightParen
>         conPattern f ts c = ConstructorPattern () (f c) ts

> constrTerm2 :: Parser Token (ConstrTerm ()) a
> constrTerm2 = literalPattern <|> anonPattern <|> identPattern
>           <|> parenPattern <|> listPattern <|> lazyPattern

> literalPattern :: Parser Token (ConstrTerm ()) a
> literalPattern = LiteralPattern () <$> literal

> anonPattern :: Parser Token (ConstrTerm ()) a
> anonPattern = VariablePattern () anonId <$-> token Underscore

> identPattern :: Parser Token (ConstrTerm ()) a
> identPattern = varId <**> optAsPattern
>            <|> qConId <\> varId <**> optRecPattern

> parenPattern :: Parser Token (ConstrTerm ()) a
> parenPattern = leftParen <-*> parenPattern
>   where parenPattern = minus <**> minusPattern negNum
>                    <|> fminus <**> minusPattern negFloat
>                    <|> funSym <\> minus <\> fminus <*-> rightParen
>                                                    <**> optAsPattern
>                    <|> (gconSym <\> funSym) <*-> rightParen <**> optRecPattern
>                    <|> parenTuplePattern <\> minus <\> fminus <*-> rightParen
>         minusPattern p = rightParen <-*> optAsPattern
>                      <|> parenMinusPattern p <*-> rightParen

> listPattern :: Parser Token (ConstrTerm ()) a
> listPattern = ListPattern () <$> brackets (constrTerm0 `sepBy` comma)

> lazyPattern :: Parser Token (ConstrTerm ()) a
> lazyPattern = LazyPattern <$-> token Tilde <*> constrTerm2

\end{verbatim}
Partial patterns used in the combinators above, but also for parsing
the left-hand side of a declaration.
\begin{verbatim}

> gconSym :: Parser Token QualIdent a
> gconSym = gConSym <|> tupleCommas

> negNum,negFloat :: Parser Token (Ident -> ConstrTerm ()) a
> negNum = negPattern <$> (Int <$> int <|> Float <$> float)
>   where negPattern l op = NegativePattern () op l
> negFloat = negPattern . Float <$> (fromIntegral <$> int <|> float)
>   where negPattern l op = NegativePattern () op l

> optAsPattern :: Parser Token (Ident -> ConstrTerm ()) a
> optAsPattern = flip AsPattern <$-> token At <*> constrTerm2
>            <|> flip (RecordPattern () . qualify) <$> fields constrTerm0
>          `opt` VariablePattern ()

> optRecPattern :: Parser Token (QualIdent -> ConstrTerm ()) a
> optRecPattern = recPattern <$> fields constrTerm0
>           `opt` conPattern
>   where conPattern c = ConstructorPattern () c []
>         recPattern fs c = RecordPattern () c fs

> optInfixPattern :: Parser Token (ConstrTerm () -> ConstrTerm ()) a
> optInfixPattern = infixPat <$> gconop <*> constrTerm0
>             `opt` id
>   where infixPat op t2 t1 = InfixPattern () t1 op t2

> optTuplePattern :: Parser Token (ConstrTerm () -> ConstrTerm ()) a
> optTuplePattern = tuple <$> many1 (comma <-*> constrTerm0)
>             `opt` ParenPattern
>   where tuple ts t = TuplePattern (t:ts)

> parenMinusPattern :: Parser Token (Ident -> ConstrTerm ()) a
>                   -> Parser Token (Ident -> ConstrTerm ()) a
> parenMinusPattern p = p <.> optInfixPattern <.> optTuplePattern

> parenTuplePattern :: Parser Token (ConstrTerm ()) a
> parenTuplePattern = constrTerm0 <**> optTuplePattern
>               `opt` ConstructorPattern () qUnitId []

\end{verbatim}
\paragraph{Expressions}
\begin{verbatim}

> condExpr :: Parser Token a b -> Parser Token (CondExpr ()) b
> condExpr eq = CondExpr <$> position <*-> bar <*> expr0 <*-> eq <*> expr

> expr :: Parser Token (Expression ()) a
> expr = expr0 <**?> (flip Typed <$-> token DoubleColon <*> type0)

> expr0 :: Parser Token (Expression ()) a
> expr0 = expr1 `chainr1` (flip InfixApply <$> infixOp)

> expr1 :: Parser Token (Expression ()) a
> expr1 = UnaryMinus <$> (minus <|> fminus) <*> expr2
>     <|> expr2

> expr2 :: Parser Token (Expression ()) a
> expr2 = lambdaExpr <|> letExpr <|> doExpr <|> ifExpr <|> caseExpr
>     <|> foldl1 Apply <$> many1 expr3

> expr3 :: Parser Token (Expression ()) a
> expr3 = foldl RecordUpdate <$> expr4 <*> many recUpdate
>   where recUpdate = braces (field expr0 `sepBy1` comma)

> expr4 :: Parser Token (Expression ()) a
> expr4 = constant <|> variable <|> parenExpr <|> listExpr

> constant :: Parser Token (Expression ()) a
> constant = Literal () <$> literal

> variable :: Parser Token (Expression ()) a
> variable = qFunId <**> optRecord
>   where optRecord = flip (Record ()) <$> fields expr0
>               `opt` Variable ()

> parenExpr :: Parser Token (Expression ()) a
> parenExpr = leftParen <-*> pExpr
>   where pExpr = (minus <|> fminus) <**> minusOrTuple
>             <|> Constructor () <$> tupleCommas <*-> rightParen
>             <|> leftSectionOrTuple <\> minus <\> fminus <*-> rightParen
>             <|> opOrRightSection <\> minus <\> fminus
>             <|> Constructor () qUnitId <$-> rightParen
>         minusOrTuple = flip UnaryMinus <$> expr1 <.> infixOrTuple
>                                        <*-> rightParen
>                    <|> rightParen <-*> optRecord qualify Variable
>         leftSectionOrTuple = expr1 <**> infixOrTuple
>         infixOrTuple = ($ id) <$> infixOrTuple'
>         infixOrTuple' = infixOp <**> leftSectionOrExp
>                     <|> (.) <$> (optType <.> tupleExpr)
>         leftSectionOrExp = expr1 <**> (infixApp <$> infixOrTuple')
>                      `opt` leftSection
>         optType = flip Typed <$-> token DoubleColon <*> type0
>             `opt` id
>         tupleExpr = tuple <$> many1 (comma <-*> expr)
>               `opt` Paren
>         opOrRightSection = qFunSym <**> optRightSection InfixOp Variable
>                        <|> colon <**> optRightSection InfixConstr Constructor
>                        <|> infixOp <\> colon <\> qFunSym <**> rightSection
>                                                          <*-> rightParen
>         optRightSection op var = (. op ()) <$> rightSection <*-> rightParen
>                              <|> rightParen <-*> optRecord id var
>         rightSection = flip RightSection <$> expr0
>         optRecord f var = flip (Record () . f) <$> fields expr0
>                     `opt` var () . f
>         infixApp f e2 op g e1 = f (g . InfixApply e1 op) e2
>         leftSection op f e = LeftSection (f e) op
>         tuple es e = Tuple (e:es)

> infixOp :: Parser Token (InfixOp ()) a
> infixOp = InfixOp () <$> qfunop
>       <|> InfixConstr () <$> colon

> listExpr :: Parser Token (Expression ()) a
> listExpr = brackets (elements `opt` List () [])
>   where elements = expr <**> rest
>         rest = comprehension
>            <|> enumeration (flip EnumFromTo) EnumFrom
>            <|> comma <-*> expr <**>
>                (enumeration (flip3 EnumFromThenTo) (flip EnumFromThen)
>                <|> (\es e2 e1 -> List () (e1:e2:es)) <$>
>                    many (comma <-*> expr))
>          `opt` (\e -> List () [e])
>         comprehension = flip ListCompr <$-> bar <*> quals
>         enumeration enumTo enum =
>           token DotDot <-*> (enumTo <$> expr `opt` enum)
>         flip3 f x y z = f z y x

> lambdaExpr :: Parser Token (Expression ()) a
> lambdaExpr = Lambda <$> position <*-> token Backslash <*> many1 constrTerm2
>                     <*-> (token RightArrow <?> "-> expected") <*> expr

> letExpr :: Parser Token (Expression ()) a
> letExpr = Let <$-> token KW_let <*> localDecls
>               <*-> (token KW_in <?> "in expected") <*> expr

> doExpr :: Parser Token (Expression ()) a
> doExpr = uncurry Do <$-> token KW_do <*> layout stmts

> ifExpr :: Parser Token (Expression ()) a
> ifExpr = IfThenElse <$-> token KW_if <*> expr
>                     <*-> (token KW_then <?> "then expected") <*> expr
>                     <*-> (token KW_else <?> "else expected") <*> expr

> caseExpr :: Parser Token (Expression ()) a
> caseExpr = Case <$-> token KW_case <*> expr
>                 <*-> (token KW_of <?> "of expected") <*> layout alts

> alts :: Parser Token [Alt ()] a
> alts = (:) <$> alt <*> semiBlock (block alt) []
>    <|> semicolon <-*> alts

> alt :: Parser Token (Alt ()) a
> alt = Alt <$> position <*> constrTerm0
>           <*> rhs (token RightArrow <?> "-> expected")

> fields :: Parser Token a b -> Parser Token [Field a] b
> fields p = braces (field p `sepBy` comma)

> field :: Parser Token a b -> Parser Token (Field a) b
> field p = Field <$> qfun <*-> equals <*> p

\end{verbatim}
\paragraph{Statements in list comprehensions and \texttt{do} expressions}
Parsing statements is a bit difficult because the syntax of patterns
and expressions largely overlaps. The parser will first try to
recognize the prefix \emph{Pattern}~\texttt{<-} of a binding statement
and if this fails fall back into parsing an expression statement. In
addition, we have to be prepared that the sequence
\texttt{let}~\emph{LocalDefs} can be either a let-statement or the
prefix of a let expression.
\begin{verbatim}

> stmts :: Parser Token ([Statement ()],Expression ()) a
> stmts = stmt reqStmts optStmts
>     <|> semicolon <-*> stmts

> reqStmts :: Parser Token (Statement () -> ([Statement ()],Expression ())) a
> reqStmts = (\(sts,e) st -> (st : sts,e)) <$-> semicolon <*> stmts

> optStmts :: Parser Token (Expression () -> ([Statement ()],Expression ())) a
> optStmts = semicolon <-*> optStmts'
>      `opt` (,) []
> optStmts' = (\(sts,e) st -> (StmtExpr st : sts,e)) <$> stmts
>       `opt` ((,) [])

> quals :: Parser Token [Statement ()] a
> quals = stmt (succeed id) (succeed StmtExpr) `sepBy1` comma

> stmt :: Parser Token (Statement () -> a) b
>      -> Parser Token (Expression () -> a) b
>      -> Parser Token a b
> stmt stmtCont exprCont = letStmt stmtCont exprCont
>                      <|> exprOrBindStmt stmtCont exprCont

> letStmt :: Parser Token (Statement () -> a) b
>         -> Parser Token (Expression () -> a) b
>         -> Parser Token a b
> letStmt stmtCont exprCont = token KW_let <-*> localDecls <**> optExpr
>   where optExpr = flip Let <$-> token KW_in <*> expr <.> exprCont
>               <|> succeed StmtDecl <.> stmtCont

> exprOrBindStmt :: Parser Token (Statement () -> a) b
>                -> Parser Token (Expression () -> a) b
>                -> Parser Token a b
> exprOrBindStmt stmtCont exprCont =
>        StmtBind <$> position <*> constrTerm0 <*-> leftArrow <*> expr
>                 <**> stmtCont
>   <|?> expr <\> token KW_let <**> exprCont

\end{verbatim}
\paragraph{Literals, identifiers, and (infix) operators}
\begin{verbatim}

> char :: Parser Token Char a
> char = cval <$> token CharTok

> int :: Parser Token Integer a
> int = ival <$> token IntTok

> float :: Parser Token Double a
> float = fval <$> token FloatTok

> string :: Parser Token String a
> string = sval <$> token StringTok

> tycon, tyvar :: Parser Token Ident a
> tycon = conId
> tyvar = varId

> qtycon :: Parser Token QualIdent a
> qtycon = qConId

> varId, funId, conId :: Parser Token Ident a
> varId = ident
> funId = ident
> conId = ident

> funSym, conSym :: Parser Token Ident a
> funSym = sym
> conSym = sym

> var, fun, con :: Parser Token Ident a
> var = varId <|> parens (funSym <?> "operator symbol expected")
> fun = funId <|> parens (funSym <?> "operator symbol expected")
> con = conId <|> parens (conSym <?> "operator symbol expected")

> funop, conop :: Parser Token Ident a
> funop = funSym <|> backquotes (funId <?> "operator name expected")
> conop = conSym <|> backquotes (conId <?> "operator name expected")

> qFunId, qConId :: Parser Token QualIdent a
> qFunId = qIdent
> qConId = qIdent

> qFunSym, qConSym :: Parser Token QualIdent a
> qFunSym = qSym
> qConSym = qSym
> gConSym = qConSym <|> colon

> qfun, qcon :: Parser Token QualIdent a
> qfun = qFunId <|> parens (qFunSym <?> "operator symbol expected")
> qcon = qConId <|> parens (qConSym <?> "operator symbol expected")

> qfunop, qconop, gconop :: Parser Token QualIdent a
> qfunop = qFunSym <|> backquotes (qFunId <?> "operator name expected")
> qconop = qConSym <|> backquotes (qConId <?> "operator name expected")
> gconop = gConSym <|> backquotes (qConId <?> "operator name expected")

> specialIdents, specialSyms :: [Category]
> specialIdents = [Id_as,Id_ccall,Id_forall,Id_hiding,Id_interface,
>                  Id_primitive,Id_qualified,Id_rawcall,Id_safe,Id_unsafe]
> specialSyms = [Sym_Dot,Sym_Minus,Sym_MinusDot]

> ident :: Parser Token Ident a
> ident = mkIdent . sval <$> tokens (Id : specialIdents)

> qIdent :: Parser Token QualIdent a
> qIdent = qualify <$> ident <|> mkQIdent <$> token QId
>   where mkQIdent a = qualifyWith (mkMIdent (modul a)) (mkIdent (sval a))

> mIdent :: Parser Token ModuleIdent a
> mIdent = mIdent <$> tokens (Id : QId : specialIdents)
>   where mIdent a = mkMIdent (modul a ++ [sval a])

> sym :: Parser Token Ident a
> sym = mkIdent . sval <$> tokens (Sym : specialSyms)

> qSym :: Parser Token QualIdent a
> qSym = qualify <$> sym <|> mkQIdent <$> token QSym
>   where mkQIdent a = qualifyWith (mkMIdent (modul a)) (mkIdent (sval a))

> colon :: Parser Token QualIdent a
> colon = qConsId <$-> token Colon

> minus :: Parser Token Ident a
> minus = minusId <$-> token Sym_Minus

> fminus :: Parser Token Ident a
> fminus = fminusId <$-> token Sym_MinusDot

> tupleCommas :: Parser Token QualIdent a
> tupleCommas = qTupleId . (1 + ) . length <$> many1 comma

\end{verbatim}
\paragraph{Layout}
\begin{verbatim}

> layout :: Parser Token a b -> Parser Token a b
> layout p = braces p
>        <|> layoutOn <-*> (p <\> token VRightBrace <\> token VSemicolon)
>                     <*-> layoutEnd
>                     <*-> (token VRightBrace `opt` NoAttributes)

> block :: Parser Token a b -> Parser Token [a] b
> block p = q
>   where q = (:) <$> p <?*> semiBlock q []

> semiBlock :: Parser Token a b -> a -> Parser Token a b
> semiBlock ds z = semicolon <-*> ds `opt` z

\end{verbatim}
\paragraph{More combinators}
Note that the \texttt{braces} combinator turns off layout processing
at the opening brace and restores the current layout mode at the
closing brace. Due to the one token look-ahead of the parsing
combinators, layout processing must be changed \emph{before} consuming
the opening and closing brace, respectively.
\begin{verbatim}

> braces, brackets, parens, backquotes :: Parser Token a b -> Parser Token a b
> braces p = bracket (layoutOff <-*> leftBrace) p (layoutEnd <-*> rightBrace)
> brackets p = bracket leftBracket p rightBracket
> parens p = bracket leftParen p rightParen
> backquotes p = bracket backquote p checkBackquote

> option :: Parser Token a b -> Parser Token (Maybe a) b
> option p = Just <$> p `opt` Nothing

> flag :: Parser Token a b -> Parser Token Bool b
> flag p = True <$-> p `opt` False

\end{verbatim}
\paragraph{Simple token parsers}
\begin{verbatim}

> token :: Category -> Parser Token Attributes a
> token c = attr <$> symbol (Token c NoAttributes)
>   where attr (Token _ a) = a

> tokens :: [Category] -> Parser Token Attributes a
> tokens cs = foldr1 (<|>) (map token cs)

> tokenOps :: [(Category,a)] -> Parser Token a b
> tokenOps cs = ops [(Token c NoAttributes,x) | (c,x) <- cs]

> dot, comma, semicolon, bar, equals :: Parser Token Attributes a
> dot = token Sym_Dot
> comma = token Comma
> semicolon = token Semicolon <|> token VSemicolon
> bar = token Bar
> equals = token Equals

> backquote, checkBackquote :: Parser Token Attributes a
> backquote = token Backquote
> checkBackquote = backquote <?> "backquote (`) expected"

> leftParen, rightParen :: Parser Token Attributes a
> leftParen = token LeftParen
> rightParen = token RightParen

> leftBracket, rightBracket :: Parser Token Attributes a
> leftBracket = token LeftBracket
> rightBracket = token RightBracket

> leftBrace, rightBrace :: Parser Token Attributes a
> leftBrace = token LeftBrace
> rightBrace = token RightBrace

> leftArrow :: Parser Token Attributes a
> leftArrow = token LeftArrow

\end{verbatim}
