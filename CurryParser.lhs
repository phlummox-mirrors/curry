% -*- LaTeX -*-
% $Id: CurryParser.lhs 3168 2015-08-26 13:58:22Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryParser.lhs}
\section{A Parser for Curry}
The Curry parser is implemented using the (mostly) LL(1) parsing
combinators described in appendix~\ref{sec:ll-parsecomb}.
\begin{verbatim}

> module CurryParser(parseSource, parseHeader, parseInterface, parseGoal) where
> import Applicative
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
> parseHeader fn = prefixParser (moduleHeader fn <*
>                                (leftBrace <|> layoutOn) <*>
>                                importDecls <*>
>                                pure [])
>                               lexer
>                               fn
>   where importDecls = (:) <$> importDecl <*> importDecls' `opt` []
>         importDecls' = semicolon *> importDecls `opt` []

> parseModule :: FilePath -> Parser r Token (Module ())
> parseModule fn = uncurry <$> moduleHeader fn <*> layout moduleDecls

> moduleHeader :: FilePath
>              -> Parser r Token ([ImportDecl] -> [TopDecl ()] -> Module ())
> moduleHeader fn = Module <$ token KW_module
>                          <*> (mIdent <?> "module name expected")
>                          <*> optional exportSpec
>                          <* (token KW_where <?> "where expected")
>             `opt` Module (defaultMIdent fn) Nothing

> exportSpec :: Parser r Token ExportSpec
> exportSpec = Exporting <$> position <*> parens (export `sepBy` comma)

> export :: Parser r Token Export
> export = qtycon <**> (parens spec `opt` Export)
>      <|> Export <$> qfun <\> qtycon
>      <|> ExportModule <$ token KW_module <*> mIdent
>   where spec = ExportTypeAll <$ token DotDot
>            <|> flip ExportTypeWith <$> con `sepBy` comma

> moduleDecls :: Parser r Token ([ImportDecl],[TopDecl ()])
> moduleDecls = imp <$> importDecl <?*> semiBlock moduleDecls ([],[])
>           <|> top <$> topDecl <*> semiBlock (block topDecl) []
>   where imp i ~(is,ds) = (i:is,ds)
>         top d ds = ([],d:ds)

> importDecl :: Parser r Token ImportDecl
> importDecl =
>   flip . ImportDecl <$> position <* token KW_import
>                     <*> flag (token Id_qualified)
>                     <*> mIdent
>                     <*> optional (token Id_as *> mIdent)
>                     <*> optional importSpec

> importSpec :: Parser r Token ImportSpec
> importSpec = position <**> (Hiding <$ token Id_hiding `opt` Importing)
>                       <*> parens (spec `sepBy` comma)
>   where spec = tycon <**> (parens constrs `opt` Import)
>            <|> Import <$> fun <\> tycon
>         constrs = ImportTypeAll <$ token DotDot
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

> parseIntf :: Parser r Token Interface
> parseIntf = uncurry <$> intfHeader <*> braces intfDecls

> intfHeader :: Parser r Token ([IImportDecl] -> [IDecl] -> Interface)
> intfHeader = Interface <$ token Id_interface <*> moduleName
>                        <* (token KW_where <?> "where expected")
>   where moduleName = mIdent
>                  <|> mkMIdent . return <$> string
>                  <?> "module name expected"

> intfDecls :: Parser r Token ([IImportDecl],[IDecl])
> intfDecls = imp <$> iImportDecl <?*> semiBlock intfDecls ([],[])
>         <|> intf <$> intfDecl <*> semiBlock (block intfDecl) []
>   where imp i ~(is,ds) = (i:is,ds)
>         intf d ds = ([],d:ds)

> iImportDecl :: Parser r Token IImportDecl
> iImportDecl = IImportDecl <$> position <* token KW_import <*> mIdent

\end{verbatim}
\paragraph{Goals}
\begin{verbatim}

> parseGoal :: String -> Error (Goal ())
> parseGoal s = applyParser goal lexer "" s

> goal :: Parser r Token (Goal ())
> goal = Goal <$> position <*> expr <*> whereClause

\end{verbatim}
\paragraph{Declarations}
\begin{verbatim}

> topDecl :: Parser r Token (TopDecl ())
> topDecl = dataDecl <|> newtypeDecl <|> typeDecl <|> BlockDecl <$> blockDecl
>   where blockDecl = infixDecl <|> typeSig <|?> functionDecl <|> foreignDecl
>                 <|> trustAnnotation

> whereClause :: Parser r Token [Decl ()]
> whereClause = token KW_where *> localDecls
>         `opt` []

> localDecls :: Parser r Token [Decl ()]
> localDecls = layout (block localDecl)

> localDecl :: Parser r Token (Decl ())
> localDecl = infixDecl <|> typeSig <|?> valueDecl <|?> freeDecl <|> foreignDecl
>         <|> trustAnnotation

> dataDecl :: Parser r Token (TopDecl ())
> dataDecl = typeDeclLhs DataDecl KW_data <*> constrs
>   where constrs = equals *> constrDecl `sepBy1` bar
>             `opt` []

> newtypeDecl :: Parser r Token (TopDecl ())
> newtypeDecl = typeDeclLhs NewtypeDecl KW_newtype <* equals <*> newConstrDecl

> typeDecl :: Parser r Token (TopDecl ())
> typeDecl = typeDeclLhs TypeDecl KW_type <* equals <*> type0

> typeDeclLhs :: (Position -> Ident -> [Ident] -> a) -> Category
>             -> Parser r Token a
> typeDeclLhs f kw = f <$> position <* token kw <*> gtycon <*> many typeVar
>   where typeVar = tyvar <|> anonId <$ token Underscore
>         gtycon = tycon <|> ptycon

> ptycon :: Parser r Token Ident
> ptycon = brackets (pure listId) <|> parens tupleCommas

> constrDecl :: Parser r Token ConstrDecl
> constrDecl = position <**> (existVars <**> constr)
>   where existVars = token Id_forall *> some tyvar <* dot `opt` []
>         constr = conId <**> identDecl
>              <|> leftParen *> parenDecl
>              <|> leftBracket *> bracketDecl
>              <|> type1 <\> conId <\> leftParen <\> leftBracket <**> opDecl
>         identDecl = many type2 <**> (conType <$> opDecl `opt` conDecl)
>                 <|> recDecl <$> fields
>         parenDecl = (conSym <|> colon) <* rightParen <**> opSymDecl
>                 <|> tupleCommas <* rightParen <**> identDecl
>                 <|> (tupleType <* rightParen) <\> rightParen <**> opDecl
>         bracketDecl = conDecl [] nilId <$ rightBracket
>                   <|> ListType <$> type0 <* rightBracket <**> opDecl
>         opSymDecl = conDecl <$> many type2
>                 <|> recDecl <$> fields
>         opDecl = conOpDecl <$> (conop <|> colon) <*> type1
>         fields = braces (fieldDecl `sepBy` comma)
>         conType f tys c = f (ConstructorType (qualify c) tys)
>         conDecl tys c tvs p = ConstrDecl p tvs c tys
>         conOpDecl op ty2 ty1 tvs p = ConOpDecl p tvs ty1 op ty2
>         recDecl fs c tvs p = RecordDecl p tvs c fs

> fieldDecl :: Parser r Token FieldDecl
> fieldDecl = FieldDecl <$> position <*> labels <* token DoubleColon <*> type0
>   where labels = fun `sepBy1` comma

> newConstrDecl :: Parser r Token NewConstrDecl
> newConstrDecl = position <**> (con <**> newConstr)
>   where newConstr = newConDecl <$> type2
>                 <|> newRecDecl <$> braces newFieldDecl
>         newConDecl ty c p = NewConstrDecl p c ty
>         newRecDecl (l,ty) c p = NewRecordDecl p c l ty

> newFieldDecl :: Parser r Token (Ident,TypeExpr)
> newFieldDecl = (,) <$> fun <* token DoubleColon <*> type0

> infixDecl :: Parser r Token (Decl ())
> infixDecl =
>   infixDeclLhs InfixDecl <*> optional int <*> (funop <|> colon) `sepBy1` comma

> infixDeclLhs :: (Position -> Infix -> a) -> Parser r Token a
> infixDeclLhs f = f <$> position <*> tokenOps infixKW
>   where infixKW = [(KW_infix,Infix),(KW_infixl,InfixL),(KW_infixr,InfixR)]

> typeSig :: Parser r Token (Decl ())
> typeSig =
>   TypeSig <$> position <*> fun `sepBy1` comma <* token DoubleColon <*> type0

> functionDecl :: Parser r Token (Decl ())
> functionDecl = funDecl <$> position <*> lhs <*> declRhs
>   where lhs = (\f -> (f,FunLhs f [])) <$> fun
>          <|?> funLhs

> valueDecl :: Parser r Token (Decl ())
> valueDecl = valDecl <$> position <*> constrTerm0 <*> declRhs
>        <|?> funDecl <$> position <*> curriedLhs <*> declRhs
>   where valDecl p (ConstructorPattern _ c ts)
>           | not (isConstrId c) = funDecl p (f,FunLhs f ts)
>           where f = unqualify c
>         valDecl p t = opDecl p id t
>         opDecl p f (InfixPattern a1 t1 (InfixConstr a2 op) t2)
>           | isConstrId op =
>               opDecl p (f . InfixPattern a1 t1 (InfixConstr a2 op)) t2
>           | otherwise = funDecl p (op',OpLhs (f t1) op' t2)
>           where op' = unqualify op
>         opDecl p f t = PatternDecl p (f t)
>         isConstrId c = isQualified c || isPrimDataId (unqualify c)

> funDecl :: Position -> (Ident,Lhs ()) -> Rhs () -> Decl ()
> funDecl p (f,lhs) rhs = FunctionDecl p () f [Equation p lhs rhs]

> funLhs :: Parser r Token (Ident,Lhs ())
> funLhs = funLhs <$> fun <*> some constrTerm2
>     <|?> flip ($ id) <$> constrTerm1 <*> opLhs'
>     <|?> curriedLhs
>   where opLhs' = opLhs <$> funSym <*> constrTerm0
>              <|> infixPat <$> gConSym <\> funSym <*> constrTerm1 <*> opLhs'
>              <|> backquote *> opIdLhs
>         opIdLhs = opLhs <$> funId <* checkBackquote <*> constrTerm0
>               <|> infixPat <$> qConId <\> funId <* backquote <*> constrTerm1
>                            <*> opLhs'
>         funLhs f ts = (f,FunLhs f ts)
>         opLhs op t2 f t1 = (op,OpLhs (f t1) op t2)
>         infixPat op t2 f g t1 =
>           f (g . InfixPattern () t1 (InfixConstr () op)) t2

> curriedLhs :: Parser r Token (Ident,Lhs ())
> curriedLhs = apLhs <$> parens funLhs <*> some constrTerm2
>   where apLhs (f,lhs) ts = (f,ApLhs lhs ts)

> declRhs :: Parser r Token (Rhs ())
> declRhs = rhs equals

> rhs :: Parser r Token a -> Parser r Token (Rhs ())
> rhs eq = rhsExpr <*> whereClause
>   where rhsExpr = SimpleRhs <$ eq <*> position <*> expr
>               <|> GuardedRhs <$> some (condExpr eq)

> freeDecl :: Parser r Token (Decl ())
> freeDecl = FreeDecl <$> position <*> fvar `sepBy1` comma <* token KW_free
>   where fvar = FreeVar () <$> var

> foreignDecl :: Parser r Token (Decl ())
> foreignDecl =
>   mkDecl <$> position <* token KW_foreign <* token KW_import
>          <*> callConv <*> entitySpec <* token DoubleColon <*> type0
>   where mkDecl p cc (s,ie,f) ty = ForeignDecl p (cc,s,ie) () f ty
>         callConv = CallConvPrimitive <$ token Id_primitive
>                <|> CallConvCCall <$ token Id_ccall
>                <|> CallConvRawCall <$ token Id_rawcall
>         entitySpec = withSafety <$> safety <*> optional importSpec
>                  <|> withoutSafety <$> importSpec <\> safety
>         safety = (,) Unsafe <$> token Id_unsafe
>              <|> (,) Safe <$> token Id_safe
>         importSpec = (,) <$> optional string <*> fun
>         withSafety s (Just (ie,f)) = (Just (fst s),ie,f)
>         withSafety s Nothing =  (Nothing,Nothing,mkIdent (sval (snd s)))
>         withoutSafety (ie,f) = (Nothing,ie,f)

> trustAnnotation :: Parser r Token (Decl ())
> trustAnnotation =
>   TrustAnnot <$> position <*> tokenOps pragmaKW <*> funList <* token PragmaEnd
>   where pragmaKW = [(PragmaBegin SuspectPragma,Suspect),
>                     (PragmaBegin TrustPragma,Trust)]
>         funList = fun `sepBy` comma
>               <|> [] <$ token Underscore              -- backward compability

\end{verbatim}
\paragraph{Interface declarations}
\begin{verbatim}

> intfDecl :: Parser r Token IDecl
> intfDecl = iInfixDecl
>        <|> hidingDataDecl <|> iDataDecl <|> iNewtypeDecl <|> iTypeDecl
>        <|> iFunctionDecl

> iInfixDecl :: Parser r Token IDecl
> iInfixDecl = infixDeclLhs IInfixDecl <*> int <*> (qfunop <|> qcolon)

> hidingDataDecl :: Parser r Token IDecl
> hidingDataDecl =
>   position <**> pragma DataPragma (dataDecl <$> qtycon <*> many tyvar)
>   where dataDecl tc tvs p = HidingDataDecl p tc tvs

> iDataDecl :: Parser r Token IDecl
> iDataDecl = iTypeDeclLhs IDataDecl KW_data <*> constrs <*> iHidden
>   where constrs = equals *> constrDecl `sepBy1` bar
>             `opt` []

> iNewtypeDecl :: Parser r Token IDecl
> iNewtypeDecl =
>   iTypeDeclLhs INewtypeDecl KW_newtype <* equals <*> newConstrDecl <*> iHidden

> iTypeDecl :: Parser r Token IDecl
> iTypeDecl = iTypeDeclLhs ITypeDecl KW_type <* equals <*> type0

> iTypeDeclLhs :: (Position -> QualIdent -> [Ident] -> a) -> Category
>              -> Parser r Token a
> iTypeDeclLhs f kw = f <$> position <* token kw <*> gtycon <*> many tyvar
>   where gtycon = qtycon <|> qualify <$> ptycon

> iHidden :: Parser r Token [Ident]
> iHidden = pragma HidingPragma (con `sepBy` comma)
>     `opt` []

> iFunctionDecl :: Parser r Token IDecl
> iFunctionDecl =
>   IFunctionDecl <$> position <*> qfun <* token DoubleColon
>                 <*> optional iFunctionArity <*> type0

> iFunctionArity :: Parser r Token Integer
> iFunctionArity = pragma ArityPragma int

> pragma :: Pragma -> Parser r Token a -> Parser r Token a
> pragma kw p = token (PragmaBegin kw) *> p <* token PragmaEnd

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> type0 :: Parser r Token TypeExpr
> type0 = type1 `chainr1` (ArrowType <$ token RightArrow)

> type1 :: Parser r Token TypeExpr
> type1 = ConstructorType <$> qtycon <*> many type2
>     <|> type2 <\> qtycon

> type2 :: Parser r Token TypeExpr
> type2 = anonType <|> identType <|> parenType <|> listType

> anonType :: Parser r Token TypeExpr
> anonType = VariableType anonId <$ token Underscore

> identType :: Parser r Token TypeExpr
> identType = VariableType <$> tyvar
>         <|> flip ConstructorType [] <$> qtycon <\> tyvar

> parenType :: Parser r Token TypeExpr
> parenType = parens tupleType

> tupleType :: Parser r Token TypeExpr
> tupleType = type0 <**?> (tuple <$> some (comma *> type0))
>       `opt` ConstructorType (qualify unitId) []
>   where tuple tys ty = TupleType (ty:tys)

> listType :: Parser r Token TypeExpr
> listType = ListType <$> brackets type0

\end{verbatim}
\paragraph{Literals}
\begin{verbatim}

> literal :: Parser r Token Literal
> literal = Char <$> char
>       <|> Int <$> int
>       <|> Float <$> float
>       <|> String <$> string

\end{verbatim}
\paragraph{Patterns}
\begin{verbatim}

> constrTerm0 :: Parser r Token (ConstrTerm ())
> constrTerm0 = constrTerm1 `chainr1` (infixPat <$> infixCon)
>   where infixPat op t1 t2 = InfixPattern () t1 op t2

> constrTerm1 :: Parser r Token (ConstrTerm ())
> constrTerm1 = varId <**> identPattern
>           <|> qConId <\> varId <**> constrPattern
>           <|> minus <**> negNum
>           <|> fminus <**> negFloat
>           <|> leftParen *> parenPattern
>           <|> constrTerm2 <\> qConId <\> leftParen
>   where identPattern = optAsPattern
>                    <|> conPattern qualify <$> some constrTerm2
>         constrPattern = conPattern id <$> some constrTerm2
>                     <|> optRecPattern
>         parenPattern = minus <**> minusPattern negNum
>                    <|> fminus <**> minusPattern negFloat
>                    <|> funSym <\> minus <\> fminus <* rightParen
>                                                    <**> identPattern
>                    <|> gconSym <\> funSym <* rightParen <**> constrPattern
>                    <|> parenTuplePattern <\> minus <\> fminus <* rightParen
>         minusPattern p = rightParen *> identPattern
>                      <|> parenMinusPattern p <* rightParen
>         conPattern f ts c = ConstructorPattern () (f c) ts

> constrTerm2 :: Parser r Token (ConstrTerm ())
> constrTerm2 = literalPattern <|> anonPattern <|> identPattern
>           <|> parenPattern <|> listPattern <|> lazyPattern

> infixCon :: Parser r Token (InfixOp ())
> infixCon = InfixConstr () <$> gconop

> literalPattern :: Parser r Token (ConstrTerm ())
> literalPattern = LiteralPattern () <$> literal

> anonPattern :: Parser r Token (ConstrTerm ())
> anonPattern = VariablePattern () anonId <$ token Underscore

> identPattern :: Parser r Token (ConstrTerm ())
> identPattern = varId <**> optAsPattern
>            <|> qConId <\> varId <**> optRecPattern

> parenPattern :: Parser r Token (ConstrTerm ())
> parenPattern = leftParen *> parenPattern
>   where parenPattern = minus <**> minusPattern negNum
>                    <|> fminus <**> minusPattern negFloat
>                    <|> funSym <\> minus <\> fminus <* rightParen
>                                                    <**> optAsPattern
>                    <|> (gconSym <\> funSym) <* rightParen <**> optRecPattern
>                    <|> parenTuplePattern <\> minus <\> fminus <* rightParen
>         minusPattern p = rightParen *> optAsPattern
>                      <|> parenMinusPattern p <* rightParen

> listPattern :: Parser r Token (ConstrTerm ())
> listPattern = ListPattern () <$> brackets (constrTerm0 `sepBy` comma)

> lazyPattern :: Parser r Token (ConstrTerm ())
> lazyPattern = LazyPattern <$ token Tilde <*> constrTerm2

\end{verbatim}
Partial patterns used in the combinators above, but also for parsing
the left-hand side of a declaration.
\begin{verbatim}

> gconSym :: Parser r Token QualIdent
> gconSym = gConSym <|> qualify <$> tupleCommas

> negNum,negFloat :: Parser r Token (Ident -> ConstrTerm ())
> negNum = negPattern <$> (Int <$> int <|> Float <$> float)
>   where negPattern l op = NegativePattern () op l
> negFloat = negPattern . Float <$> (fromIntegral <$> int <|> float)
>   where negPattern l op = NegativePattern () op l

> optAsPattern :: Parser r Token (Ident -> ConstrTerm ())
> optAsPattern = flip AsPattern <$ token At <*> constrTerm2
>            <|> flip (RecordPattern () . qualify) <$> fields constrTerm0
>          `opt` VariablePattern ()

> optRecPattern :: Parser r Token (QualIdent -> ConstrTerm ())
> optRecPattern = recPattern <$> fields constrTerm0
>           `opt` conPattern
>   where conPattern c = ConstructorPattern () c []
>         recPattern fs c = RecordPattern () c fs

> optInfixPattern :: Parser r Token (ConstrTerm () -> ConstrTerm ())
> optInfixPattern = infixPat <$> infixCon <*> constrTerm0
>             `opt` id
>   where infixPat op t2 t1 = InfixPattern () t1 op t2

> optTuplePattern :: Parser r Token (ConstrTerm () -> ConstrTerm ())
> optTuplePattern = tuple <$> some (comma *> constrTerm0)
>             `opt` ParenPattern
>   where tuple ts t = TuplePattern (t:ts)

> parenMinusPattern :: Parser r Token (Ident -> ConstrTerm ())
>                   -> Parser r Token (Ident -> ConstrTerm ())
> parenMinusPattern p = p <.> optInfixPattern <.> optTuplePattern

> parenTuplePattern :: Parser r Token (ConstrTerm ())
> parenTuplePattern = constrTerm0 <**> optTuplePattern

\end{verbatim}
\paragraph{Expressions}
\begin{verbatim}

> condExpr :: Parser r Token a -> Parser r Token (CondExpr ())
> condExpr eq = CondExpr <$> position <* bar <*> expr0 <* eq <*> expr

> expr :: Parser r Token (Expression ())
> expr = expr0 <**?> (flip Typed <$ token DoubleColon <*> type0)

> expr0 :: Parser r Token (Expression ())
> expr0 = expr1 `chainr1` (flip InfixApply <$> infixOp)

> expr1 :: Parser r Token (Expression ())
> expr1 = UnaryMinus <$> (minus <|> fminus) <*> expr2
>     <|> expr2

> expr2 :: Parser r Token (Expression ())
> expr2 = lambdaExpr <|> letExpr <|> doExpr <|> ifExpr <|> caseExpr
>     <|> foldl1 Apply <$> some expr3

> expr3 :: Parser r Token (Expression ())
> expr3 = foldl RecordUpdate <$> expr4 <*> many recUpdate
>   where recUpdate = braces (field expr0 `sepBy1` comma)

> expr4 :: Parser r Token (Expression ())
> expr4 = constant <|> anonVar <|> variable <|> parenExpr <|> listExpr

> constant :: Parser r Token (Expression ())
> constant = Literal () <$> literal

> anonVar :: Parser r Token (Expression ())
> anonVar = Variable () (qualify anonId) <$ token Underscore

> variable :: Parser r Token (Expression ())
> variable = qFunId <**> optRecord
>   where optRecord = flip (Record ()) <$> fields expr0
>               `opt` Variable ()

> parenExpr :: Parser r Token (Expression ())
> parenExpr = leftParen *> pExpr
>   where pExpr = (minus <|> fminus) <**> minusOrTuple
>             <|> leftSectionOrTuple <\> minus <\> fminus <* rightParen
>             <|> opOrRightSection <\> minus <\> fminus
>             <|> Constructor () . qualify <$> tupleCommas <* rightParen
>         minusOrTuple = flip UnaryMinus <$> expr1 <.> infixOrTuple
>                                        <* rightParen
>                    <|> rightParen *> optRecord qualify Variable
>         leftSectionOrTuple = expr1 <**> infixOrTuple
>         infixOrTuple = ($ id) <$> infixOrTuple'
>         infixOrTuple' = infixOp <**> leftSectionOrExp
>                     <|> (.) <$> (optType <.> tupleExpr)
>         leftSectionOrExp = expr1 <**> (infixApp <$> infixOrTuple')
>                      `opt` leftSection
>         optType = flip Typed <$ token DoubleColon <*> type0
>             `opt` id
>         tupleExpr = tuple <$> some (comma *> expr)
>               `opt` Paren
>         opOrRightSection = qFunSym <**> optRightSection InfixOp Variable
>                        <|> qcolon <**> optRightSection InfixConstr Constructor
>                        <|> infixOp <\> colon <\> qFunSym <**> rightSection
>                                                          <* rightParen
>         optRightSection op var = (. op ()) <$> rightSection <* rightParen
>                              <|> rightParen *> optRecord id var
>         rightSection = flip RightSection <$> expr0
>         optRecord f var = flip (Record () . f) <$> fields expr0
>                     `opt` var () . f
>         infixApp f e2 op g e1 = f (g . InfixApply e1 op) e2
>         leftSection op f e = LeftSection (f e) op
>         tuple es e = Tuple (e:es)

> infixOp :: Parser r Token (InfixOp ())
> infixOp = InfixOp () <$> qfunop
>       <|> InfixConstr () <$> qcolon

> listExpr :: Parser r Token (Expression ())
> listExpr = brackets (elements `opt` List () [])
>   where elements = expr <**> rest
>         rest = comprehension
>            <|> enumeration (flip EnumFromTo) EnumFrom
>            <|> comma *> expr <**>
>                (enumeration (flip3 EnumFromThenTo) (flip EnumFromThen)
>                 <|> (\es e2 e1 -> List () (e1:e2:es)) <$>
>                     many (comma *> expr))
>          `opt` (\e -> List () [e])
>         comprehension = flip ListCompr <$ bar <*> quals
>         enumeration enumTo enum = token DotDot *> (enumTo <$> expr `opt` enum)
>         flip3 f x y z = f z y x

> lambdaExpr :: Parser r Token (Expression ())
> lambdaExpr = Lambda <$> position <* token Backslash <*> some constrTerm2
>                     <* (token RightArrow <?> "-> expected") <*> expr

> letExpr :: Parser r Token (Expression ())
> letExpr = Let <$ token KW_let <*> localDecls
>               <* (token KW_in <?> "in expected") <*> expr

> doExpr :: Parser r Token (Expression ())
> doExpr = uncurry Do <$ token KW_do <*> layout stmts

> ifExpr :: Parser r Token (Expression ())
> ifExpr = IfThenElse <$ token KW_if <*> expr
>                     <* (token KW_then <?> "then expected") <*> expr
>                     <* (token KW_else <?> "else expected") <*> expr

> caseExpr :: Parser r Token (Expression ())
> caseExpr =
>   tokenOps caseKW <*> expr <* (token KW_of <?> "of expected") <*> layout alts
>   where caseKW = [(KW_case,Case),(KW_fcase,Fcase)]

> alts :: Parser r Token [Alt ()]
> alts = (:) <$> alt <*> semiBlock (block alt) []
>    <|> semicolon *> alts

> alt :: Parser r Token (Alt ())
> alt = Alt <$> position <*> constrTerm0
>           <*> rhs (token RightArrow <?> "-> expected")

> fields :: Parser r Token a -> Parser r Token [Field a]
> fields p = braces (field p `sepBy` comma)

> field :: Parser r Token a -> Parser r Token (Field a)
> field p = Field <$> qfun <* equals <*> p

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

> stmts :: Parser r Token ([Statement ()],Expression ())
> stmts = stmt reqStmts optStmts
>     <|> semicolon *> stmts

> reqStmts :: Parser r Token (Statement () -> ([Statement ()],Expression ()))
> reqStmts = (\(sts,e) st -> (st : sts,e)) <$ semicolon <*> stmts

> optStmts :: Parser r Token (Expression () -> ([Statement ()],Expression ()))
> optStmts = semicolon *> optStmts'
>      `opt` (,) []
> optStmts' = (\(sts,e) st -> (StmtExpr st : sts,e)) <$> stmts
>       `opt` ((,) [])

> quals :: Parser r Token [Statement ()]
> quals = stmt (pure id) (pure StmtExpr) `sepBy1` comma

> stmt :: Parser r Token (Statement () -> a)
>      -> Parser r Token (Expression () -> a)
>      -> Parser r Token a
> stmt stmtCont exprCont = letStmt stmtCont exprCont
>                      <|> exprOrBindStmt stmtCont exprCont

> letStmt :: Parser r Token (Statement () -> a)
>         -> Parser r Token (Expression () -> a)
>         -> Parser r Token a
> letStmt stmtCont exprCont = token KW_let *> localDecls <**> optExpr
>   where optExpr = flip Let <$ token KW_in <*> expr <.> exprCont
>               <|> pure StmtDecl <.> stmtCont

> exprOrBindStmt :: Parser r Token (Statement () -> a)
>                -> Parser r Token (Expression () -> a)
>                -> Parser r Token a
> exprOrBindStmt stmtCont exprCont =
>        StmtBind <$> position <*> constrTerm0 <* leftArrow <*> expr
>                 <**> stmtCont
>   <|?> expr <\> token KW_let <**> exprCont

\end{verbatim}
\paragraph{Literals, identifiers, and (infix) operators}
\begin{verbatim}

> char :: Parser r Token Char
> char = cval <$> token CharTok

> int :: Parser r Token Integer
> int = ival <$> token IntTok

> float :: Parser r Token Double
> float = fval <$> token FloatTok

> string :: Parser r Token String
> string = sval <$> token StringTok

> tycon, tyvar :: Parser r Token Ident
> tycon = conId
> tyvar = varId

> qtycon :: Parser r Token QualIdent
> qtycon = qConId

> varId, funId, conId :: Parser r Token Ident
> varId = ident
> funId = ident
> conId = ident

> funSym, conSym :: Parser r Token Ident
> funSym = sym
> conSym = sym

> var, fun, con :: Parser r Token Ident
> var = varId <|> parens (funSym <?> "operator symbol expected")
> fun = funId <|> parens (funSym <?> "operator symbol expected")
> con = conId <|> parens (conSym <?> "operator symbol expected")

> funop, conop :: Parser r Token Ident
> funop = funSym <|> backquotes (funId <?> "operator name expected")
> conop = conSym <|> backquotes (conId <?> "operator name expected")

> qFunId, qConId :: Parser r Token QualIdent
> qFunId = qIdent
> qConId = qIdent

> qFunSym, qConSym :: Parser r Token QualIdent
> qFunSym = qSym
> qConSym = qSym
> gConSym = qConSym <|> qcolon

> qfun, qcon :: Parser r Token QualIdent
> qfun = qFunId <|> parens (qFunSym <?> "operator symbol expected")
> qcon = qConId <|> parens (qConSym <?> "operator symbol expected")

> qfunop, qconop, gconop :: Parser r Token QualIdent
> qfunop = qFunSym <|> backquotes (qFunId <?> "operator name expected")
> qconop = qConSym <|> backquotes (qConId <?> "operator name expected")
> gconop = gConSym <|> backquotes (qConId <?> "operator name expected")

> specialIdents, specialSyms :: [Category]
> specialIdents = [Id_as,Id_ccall,Id_forall,Id_hiding,Id_interface,
>                  Id_primitive,Id_qualified,Id_rawcall,Id_safe,Id_unsafe]
> specialSyms = [Sym_Dot,Sym_Minus,Sym_MinusDot]

> ident :: Parser r Token Ident
> ident = mkIdent . sval <$> tokens (Id : specialIdents)

> qIdent :: Parser r Token QualIdent
> qIdent = qualify <$> ident <|> mkQIdent <$> token QId
>   where mkQIdent a = qualifyWith (mkMIdent (modul a)) (mkIdent (sval a))

> mIdent :: Parser r Token ModuleIdent
> mIdent = mIdent <$> tokens (Id : QId : specialIdents)
>   where mIdent a = mkMIdent (modul a ++ [sval a])

> sym :: Parser r Token Ident
> sym = mkIdent . sval <$> tokens (Sym : specialSyms)

> qSym :: Parser r Token QualIdent
> qSym = qualify <$> sym <|> mkQIdent <$> token QSym
>   where mkQIdent a = qualifyWith (mkMIdent (modul a)) (mkIdent (sval a))

> colon :: Parser r Token Ident
> colon = consId <$ token Colon

> qcolon :: Parser r Token QualIdent
> qcolon = qualify <$> colon

> minus :: Parser r Token Ident
> minus = minusId <$ token Sym_Minus

> fminus :: Parser r Token Ident
> fminus = fminusId <$ token Sym_MinusDot

> tupleCommas :: Parser r Token Ident
> tupleCommas = tupleId . (1 + ) . length <$> some comma `opt` unitId

\end{verbatim}
\paragraph{Layout}
\begin{verbatim}

> layout :: Parser r Token a -> Parser r Token a
> layout p = braces p
>        <|> layoutOn *> (p <\> token VRightBrace <\> token VSemicolon)
>                     <* layoutEnd
>                     <* (token VRightBrace `opt` NoAttributes)

> block :: Parser r Token a -> Parser r Token [a]
> block p = q
>   where q = (:) <$> p <?*> semiBlock q []

> semiBlock :: Parser r Token a -> a -> Parser r Token a
> semiBlock ds z = semicolon *> ds `opt` z

\end{verbatim}
\paragraph{More combinators}
Note that the \texttt{braces} combinator turns off layout processing
at the opening brace and restores the current layout mode at the
closing brace. Due to the one token look-ahead of the parsing
combinators, layout processing must be changed \emph{before} consuming
the opening and closing brace, respectively.
\begin{verbatim}

> braces, brackets, parens, backquotes :: Parser r Token a -> Parser r Token a
> braces p = bracket (layoutOff *> leftBrace) p (layoutEnd *> rightBrace)
> brackets p = bracket leftBracket p rightBracket
> parens p = bracket leftParen p rightParen
> backquotes p = bracket backquote p checkBackquote

> flag :: Parser r Token a -> Parser r Token Bool
> flag p = True <$ p `opt` False

\end{verbatim}
\paragraph{Simple token parsers}
\begin{verbatim}

> token :: Category -> Parser r Token Attributes
> token c = attr <$> symbol (Token c NoAttributes)
>   where attr (Token _ a) = a

> tokens :: [Category] -> Parser r Token Attributes
> tokens cs = foldr1 (<|>) (map token cs)

> tokenOps :: [(Category,a)] -> Parser r Token a
> tokenOps cs = ops [(Token c NoAttributes,x) | (c,x) <- cs]

> dot, comma, semicolon, bar, equals :: Parser r Token Attributes
> dot = token Sym_Dot
> comma = token Comma
> semicolon = token Semicolon <|> token VSemicolon
> bar = token Bar
> equals = token Equals

> backquote, checkBackquote :: Parser r Token Attributes
> backquote = token Backquote
> checkBackquote = backquote <?> "backquote (`) expected"

> leftParen, rightParen :: Parser r Token Attributes
> leftParen = token LeftParen
> rightParen = token RightParen

> leftBracket, rightBracket :: Parser r Token Attributes
> leftBracket = token LeftBracket
> rightBracket = token RightBracket

> leftBrace, rightBrace :: Parser r Token Attributes
> leftBrace = token LeftBrace
> rightBrace = token RightBrace

> leftArrow :: Parser r Token Attributes
> leftArrow = token LeftArrow

\end{verbatim}
