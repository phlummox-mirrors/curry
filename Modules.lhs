% -*- LaTeX -*-
% $Id: Modules.lhs 1777 2005-09-30 14:56:48Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Modules.lhs}
\section{Modules}
This module controls the compilation of modules.
\begin{verbatim}

> module Modules(compileModule,compileGoal,typeGoal) where
> import Base
> import Unlit(unlit)
> import CurryParser(parseSource,parseInterface,parseGoal)
> import ImportSyntaxCheck(checkImports)
> import TypeSyntaxCheck(typeSyntaxCheck,typeSyntaxCheckGoal)
> import SyntaxCheck(syntaxCheck,syntaxCheckGoal)
> import ExportSyntaxCheck(checkExports)
> import Renaming(rename,renameGoal)
> import PrecCheck(precCheck,precCheckGoal)
> import TypeCheck(typeCheck,typeCheckGoal)
> import IntfSyntaxCheck(intfSyntaxCheck)
> import IntfCheck(intfCheck)
> import IntfEquiv(fixInterface,intfEquiv)
> import Imports(importInterface,importInterfaceIntf,importUnifyData)
> import Exports(exportInterface)
> import Eval(evalEnv,evalEnvGoal)
> import Qual(qual,qualGoal)
> import Desugar(desugar,desugarGoal)
> import Simplify(simplify)
> import Lift(lift)
> import qualified IL
> import ILTrans(ilTrans,ilTransIntf)
> import ILLift(liftProg)
> import DTransform(dTransform,dAddMain)
> import ILCompile(camCompile,camCompileData,fun)
> import qualified CamPP(ppModule)
> import CGen(genMain,genEntry,genModule,genSplitModule)
> import CCode(CFile,mergeCFile)
> import CPretty(ppCFile)
> import CurryPP(ppModule,ppInterface,ppIDecl,ppGoal)
> import qualified ILPP(ppModule)
> import Options(Options(..),Dump(..))
> import Env
> import TopEnv
> import Combined
> import Error
> import IO
> import List
> import Maybe
> import Monad
> import PathUtils
> import Pretty
> import Typing

\end{verbatim}
The function \texttt{compileModule} is the main entry point of this
module for compiling a Curry source module. It applies syntax and type
checking to the module and translates the code into one or more C code
files. The module's interface is updated when necessary.

The compiler automatically loads the prelude when compiling a module
-- except for the prelude itself -- by adding an appropriate import
declaration to the module.
\begin{verbatim}

> compileModule :: Options -> FilePath -> ErrorT IO ()
> compileModule opts fn =
>   do
>     m <- liftErr (readFile fn) >>= okM . parseModule fn
>     mEnv <- loadInterfaces paths m
>     (tyEnv,m',intf) <- okM $ checkModule mEnv m
>     mEnv' <- importDebugPrelude paths dbg fn (bindModule intf mEnv)
>     let (ccode,dumps) = transModule split dbg trust mEnv' tyEnv m'
>         ccode' = compileDefaultGoal dbg mEnv' intf
>     liftErr $ unless (noInterface opts) (updateInterface fn intf) >>
>               mapM_ (doDump opts) dumps >>
>               writeCode (output opts) fn (merge ccode ccode')
>   where paths = importPath opts
>         split = splitCode opts
>         dbg = debug opts
>         trust = trusted opts
>         merge ccode = maybe ccode (merge' ccode)
>         merge' (Left cf1) = Left . mergeCFile cf1
>         merge' (Right cfs) = Right . (cfs ++) . return

> parseModule :: FilePath -> String -> Error Module
> parseModule fn s =
>   unlitLiterate fn s >>= liftM (importPrelude fn) . parseSource fn

> loadInterfaces :: [FilePath] -> Module -> ErrorT IO ModuleEnv
> loadInterfaces paths (Module m _ is _) =
>   foldM (loadInterface paths [m]) emptyEnv
>         [P p m | ImportDecl p m _ _ _ <- is]

> checkModule :: ModuleEnv -> Module -> Error (ValueEnv,Module,Interface)
> checkModule mEnv (Module m es is ds) =
>   do
>     (pEnv,tcEnv,tyEnv) <- importModules mEnv is
>     (tEnv,ds') <- typeSyntaxCheck m tcEnv ds
>     (vEnv,ds'') <- syntaxCheck m tyEnv ds'
>     es' <- checkExports m is tEnv vEnv es
>     (pEnv',ds''') <- precCheck m pEnv $ rename ds''
>     (tcEnv',tyEnv') <- typeCheck m tcEnv tyEnv ds'''
>     let (pEnv'',tcEnv'',tyEnv'') = qualifyEnv mEnv pEnv' tcEnv' tyEnv'
>     return (tyEnv'',
>             Module m (Just es') is (qual tyEnv' ds'''),
>             exportInterface m es' pEnv'' tcEnv'' tyEnv'')

> transModule :: Bool -> Bool -> Bool -> ModuleEnv -> ValueEnv -> Module
>             -> (Either CFile [CFile],[(Dump,Doc)])
> transModule split debug trusted mEnv tyEnv (Module m es is ds) = (ccode,dumps)
>   where evEnv = evalEnv ds
>         (desugared,tyEnv') = desugar tyEnv (Module m es is ds)
>         (simplified,tyEnv'') = simplify tyEnv' evEnv desugared
>         (lifted,tyEnv''',evEnv') = lift tyEnv'' evEnv simplified
>         il = ilTrans tyEnv''' evEnv' lifted
>         ilDbg = if debug then dTransform trusted il else il
>         ilNormal = liftProg ilDbg
>         cam = camCompile ilNormal
>         imports = camCompileData (ilImports mEnv ilNormal)
>         ccode
>           | split = Right (genSplitModule imports cam)
>           | otherwise = Left (genModule imports cam)
>         dumps =
>           [(DumpRenamed,ppModule (Module m es is ds)),
>            (DumpTypes,ppTypes m (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpSimplified,ppModule simplified),
>            (DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug ] ++
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

> qualifyEnv :: ModuleEnv -> PEnv -> TCEnv -> ValueEnv -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv mEnv pEnv tcEnv tyEnv =
>   (foldr bindQual pEnv' (localBindings pEnv),
>    foldr bindQual tcEnv' (localBindings tcEnv),
>    foldr bindGlobal tyEnv' (localBindings tyEnv))
>   where (pEnv',tcEnv',tyEnv') =
>           foldl importInterfaceIntf initEnvs (map snd (envToList mEnv))
>         bindQual (_,y) = qualBindTopEnv (origName y) y
>         bindGlobal (x,y)
>           | uniqueId x == 0 = bindQual (x,y)
>           | otherwise = bindTopEnv x y

> ilImports :: ModuleEnv -> IL.Module -> [IL.Decl]
> ilImports mEnv (IL.Module _ is _) =
>   concat [ilTransIntf i | (m,i) <- envToList mEnv, m `elem` is]

> writeCode :: Maybe FilePath -> FilePath -> Either CFile [CFile] -> IO ()
> writeCode tfn sfn (Left cfile) = writeCCode ofn cfile
>   where ofn = fromMaybe (rootname sfn ++ cExt) tfn
> writeCode tfn sfn (Right cfiles) = zipWithM_ (writeCCode . mkFn) [1..] cfiles
>   where prefix = fromMaybe (rootname sfn) tfn
>         mkFn i = prefix ++ show i ++ cExt

> writeGoalCode :: Maybe FilePath -> CFile -> IO ()
> writeGoalCode tfn = writeCCode ofn
>   where ofn = fromMaybe (internalError "No filename for startup code") tfn

> writeCCode :: FilePath -> CFile -> IO ()
> writeCCode fn = writeFile fn . showln . ppCFile

> showln :: Show a => a -> String
> showln x = shows x "\n"

\end{verbatim}
A goal is compiled with respect to a given module. If no module is
specified, the Curry prelude is used. The source module has to be
parsed and type checked before the goal can be compiled. Otherwise,
compilation of a goal is similar to that of a module.
\begin{verbatim}

> compileGoal :: Options -> Maybe String -> Maybe FilePath -> ErrorT IO ()
> compileGoal opts (Just g) fn =
>   do
>     (mEnv,_,is) <- loadGoalModule paths fn
>     (tyEnv,g') <- okM $ parseGoal g >>= checkGoal mEnv is
>     mEnv' <- importDebugPrelude paths dbg "" mEnv
>     let (ccode,dumps) = transGoal dbg run mEnv' tyEnv (mkIdent "goal") g'
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeGoalCode (output opts) (mergeCFile (genMain run) ccode)
>   where run = "curry_goal"
>         dbg = debug opts
>         paths = importPath opts
> compileGoal opts Nothing fn =
>   liftErr $ writeGoalCode (output opts) (genMain "curry_main")

> typeGoal :: Options -> String -> Maybe FilePath -> ErrorT IO ()
> typeGoal opts g fn =
>   do
>     (mEnv,m,is) <- loadGoalModule (importPath opts) fn
>     (tyEnv,Goal _ e _) <- okM $ parseGoal g >>= checkGoal mEnv is
>     liftErr $ print (ppType m (typeOf tyEnv e))

> loadGoalModule :: [FilePath] -> Maybe FilePath
>                -> ErrorT IO (ModuleEnv,ModuleIdent,[ImportDecl])
> loadGoalModule paths fn =
>   do
>     Module m _ is ds <- maybe (return emptyModule) parseGoalModule fn
>     mEnv <- loadInterfaces paths (Module m Nothing is ds)
>     (_,_,intf) <- okM $ checkModule mEnv (Module m Nothing is ds)
>     return (bindModule intf mEnv,m,is ++ [importMain m])
>   where emptyModule = importPrelude "" (Module emptyMIdent Nothing [] [])
>         parseGoalModule fn = liftErr (readFile fn) >>= okM . parseModule fn
>         importMain m = importDecl (first "") m False

> checkGoal :: ModuleEnv -> [ImportDecl] -> Goal -> Error (ValueEnv,Goal)
> checkGoal mEnv is g =
>   do
>     (pEnv,tcEnv,tyEnv) <- importModules mEnv is
>     g' <- typeSyntaxCheckGoal tcEnv g >>=
>           syntaxCheckGoal tyEnv >>=
>           precCheckGoal pEnv . renameGoal
>     tyEnv' <- typeCheckGoal tcEnv tyEnv g'
>     let (_,_,tyEnv'') = qualifyEnv mEnv pEnv tcEnv tyEnv'
>     return (tyEnv'',qualGoal tyEnv' g')

> transGoal :: Bool -> String -> ModuleEnv -> ValueEnv -> Ident -> Goal
>           -> (CFile,[(Dump,Doc)])
> transGoal debug run mEnv tyEnv goalId g = (ccode,dumps)
>   where qGoalId = qualifyWith emptyMIdent goalId
>         evEnv = evalEnvGoal g
>         (vs,desugared,tyEnv') = desugarGoal debug tyEnv emptyMIdent goalId g
>         (simplified,tyEnv'') = simplify tyEnv' evEnv desugared
>         (lifted,tyEnv''',evEnv') = lift tyEnv'' evEnv simplified
>         il = ilTrans tyEnv''' evEnv' lifted
>         ilDbg = if debug then dAddMain goalId (dTransform False il) else il
>         ilNormal = liftProg ilDbg
>         cam = camCompile ilNormal
>         imports = camCompileData (ilImports mEnv ilNormal)
>         ccode =
>           genModule imports cam ++
>           genEntry run (fun qGoalId) (fmap (map name) vs)
>         dumps =
>           [(DumpRenamed,ppGoal g),
>            (DumpTypes,ppTypes emptyMIdent (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpSimplified,ppModule simplified),
>            (DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug ] ++
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

\end{verbatim}
The compiler adds a startup function for the default goal
\texttt{main.main} to the \texttt{main} module. Thus, there is no need
to determine the type of the goal when linking the program.
\begin{verbatim}

> compileDefaultGoal :: Bool -> ModuleEnv -> Interface -> Maybe CFile
> compileDefaultGoal debug mEnv (Interface m is ds)
>   | m == mainMIdent && any (qMainId ==) [f | IFunctionDecl _ f _ <- ds] =
>       Just ccode
>   | otherwise = Nothing
>   where qMainId = qualify mainId
>         mEnv' = bindModule (Interface m is ds) mEnv
>         (tyEnv,g) = ok $
>           checkGoal mEnv' [importDecl (first "") m False]
>                     (Goal (first "") (Variable qMainId) [])
>         (ccode,_) = transGoal debug "curry_main" mEnv' tyEnv mainId g

\end{verbatim}
The function \texttt{importModules} brings the declarations of all
imported modules into scope in the current module.
\begin{verbatim}

> importModules :: ModuleEnv -> [ImportDecl] -> Error (PEnv,TCEnv,ValueEnv)
> importModules mEnv ds =
>   do
>     (pEnv,tcEnv,tyEnv) <- foldM importModule initEnvs ds
>     return (pEnv,importUnifyData tcEnv,tyEnv)
>   where importModule envs (ImportDecl _ m q asM is) =
>           do
>             is' <- checkImports i is
>             return (importInterface (fromMaybe m asM) q is' envs i)
>           where i = moduleInterface m mEnv

> moduleInterface :: ModuleIdent -> ModuleEnv -> Interface
> moduleInterface m mEnv =
>   fromMaybe (internalError "moduleInterface") (lookupModule m mEnv)

> initEnvs :: (PEnv,TCEnv,ValueEnv)
> initEnvs = (initPEnv,initTCEnv,initDCEnv)

\end{verbatim}
An implicit import of the prelude is added to the declarations of
every module, except for the prelude itself. If no explicit import for
the prelude is present, an unqualified import is inserted, otherwise
only a qualified import is added.
\begin{verbatim}

> importPrelude :: FilePath -> Module -> Module
> importPrelude fn (Module m es is ds) =
>   Module m es (if m == preludeMIdent then is else is') ds
>   where is' = importDecl (first fn) preludeMIdent q : is
>         q = preludeMIdent `elem` map importedModule is
>         importedModule (ImportDecl _ m _ asM _) = fromMaybe m asM

> importDecl :: Position -> ModuleIdent -> Bool -> ImportDecl
> importDecl p m q = ImportDecl p m q Nothing Nothing

\end{verbatim}
The module \texttt{DebugPrelude} is loaded automatically when the
program is compiled for debugging. However, no explicit import is
added to the source code because \texttt{DebugPrelude} in turn imports
the prelude. Therefore, its loading is delayed until after the source
file has been checked.
\begin{verbatim}

> importDebugPrelude :: [FilePath] -> Bool -> FilePath -> ModuleEnv
>                    -> ErrorT IO ModuleEnv
> importDebugPrelude paths dbg fn mEnv
>   | dbg = loadInterface paths [] mEnv (P (first fn) debugPreludeMIdent)
>   | otherwise = return mEnv

\end{verbatim}
If an import declaration for a module is found, the compiler first
checks whether an import for the module is already pending. In this
case the module imports are cyclic, which is not allowed in Curry, and
the compilation is aborted. Next, the compiler checks whether the
module has been imported already. If so, nothing needs to be done,
otherwise the interface is searched in the import paths and loaded if
it is found.
\begin{verbatim}

> loadInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> P ModuleIdent
>               -> ErrorT IO ModuleEnv
> loadInterface paths ctxt mEnv (P p m)
>   | m `elem` ctxt = errorAt p (cyclicImport m (takeWhile (/= m) ctxt))
>   | isJust (lookupModule m mEnv) = return mEnv
>   | otherwise =
>       liftErr (lookupInterface paths m) >>=
>       maybe (errorAt p (interfaceNotFound m))
>             (compileInterface paths ctxt mEnv m)

\end{verbatim}
After parsing an interface, all imported interfaces are recursively
loaded and entered into the interface's environment.

\ToDo{Avoid recursive loading of imported interfaces. All information
that is needed for compiling a module is present in the interfaces
that are imported directly from that module.}
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> ModuleIdent
>                  -> FilePath -> ErrorT IO ModuleEnv
> compileInterface paths ctxt mEnv m fn =
>   do
>     i@(Interface m' _ _) <- liftErr (readFile fn) >>= okM . parseInterface fn
>     unless (m == m') (errorAt (first fn) (wrongInterface m m'))
>     mEnv' <- loadIntfInterfaces paths ctxt mEnv i
>     i' <- okM (checkInterface mEnv' i)
>     return (bindModule i' mEnv')

> loadIntfInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> Interface
>                    -> ErrorT IO ModuleEnv
> loadIntfInterfaces paths ctxt mEnv (Interface m is _) =
>   foldM (loadInterface paths (m:ctxt)) mEnv [P p m | IImportDecl p m <- is]

> checkInterface :: ModuleEnv -> Interface -> Error Interface
> checkInterface mEnv (Interface m is ds) =
>   do
>     ds' <- intfSyntaxCheck ds
>     intfCheck m pEnv tcEnv tyEnv ds'
>     return (Interface m is ds')
>   where (pEnv,tcEnv,tyEnv) = foldl importModule initEnvs is
>         importModule envs (IImportDecl p m) =
>           case lookupModule m mEnv of
>             Just i -> importInterfaceIntf envs i
>             Nothing -> internalError "checkInterface"

\end{verbatim}
After checking a module successfully, the compiler may need to update
the module's interface file. The file will be updated only if the
interface has been changed or the file did not exist before.

The code below is a little bit tricky because we must make sure that the
interface file is closed before rewriting the interface -- even if it
has not been read completely. On the other hand, we must not apply
\texttt{hClose} too early. Note that there is no need to close the
interface explicitly if the interface check succeeds because the whole
file must have been read in this case. In addition, we do not update
the interface file in this case and therefore it doesn't matter when
the file is closed.
\begin{verbatim}

> updateInterface :: FilePath -> Interface -> IO ()
> updateInterface sfn i =
>   do
>     eq <- catch (matchInterface ifn i) (const (return False))
>     unless eq (writeInterface ifn i)
>   where ifn = rootname sfn ++ intfExt

> matchInterface :: FilePath -> Interface -> IO Bool
> matchInterface ifn i =
>   do
>     h <- openFile ifn ReadMode
>     s <- hGetContents h
>     case parseInterface ifn s of
>       Ok i' | i `intfEquiv` fixInterface i' -> return True
>       _ -> hClose h >> return False

> writeInterface :: FilePath -> Interface -> IO ()
> writeInterface ifn = writeFile ifn . showln . ppInterface

\end{verbatim}
The compiler searches for interface files in the import search path
using the extension \texttt{".icurry"}. Note that the current
directory is always searched first.
\begin{verbatim}

> lookupInterface :: [FilePath] -> ModuleIdent -> IO (Maybe FilePath)
> lookupInterface paths m = lookupFile (ifn : [catPath p ifn | p <- paths])
>   where ifn = foldr1 catPath (moduleQualifiers m) ++ intfExt

\end{verbatim}
Literate source files use the extension \texttt{".lcurry"}.
\begin{verbatim}

> unlitLiterate :: FilePath -> String -> Error String
> unlitLiterate fn s
>   | not (isLiterateSource fn) = return s
>   | null es = return s'
>   | otherwise = fail es
>   where (es,s') = unlit fn s

> isLiterateSource :: FilePath -> Bool
> isLiterateSource fn = litExt `isSuffixOf` fn

\end{verbatim}
The \texttt{doDump} function writes the selected information to the
standard output.
\begin{verbatim}

> doDump :: Options -> (Dump,Doc) -> IO ()
> doDump opts (d,x) =
>   when (d `elem` dump opts)
>        (print (text hd $$ text (replicate (length hd) '=') $$ x))
>   where hd = dumpHeader d

> dumpHeader :: Dump -> String
> dumpHeader DumpRenamed = "Module after renaming"
> dumpHeader DumpTypes = "Types"
> dumpHeader DumpDesugared = "Source code after desugaring"
> dumpHeader DumpSimplified = "Source code after simplification"
> dumpHeader DumpLifted = "Source code after lifting"
> dumpHeader DumpIL = "Intermediate code"
> dumpHeader DumpTransformed = "Transformed code" 
> dumpHeader DumpNormalized = "Intermediate code after normalization"
> dumpHeader DumpCam = "Abstract machine code"

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: ModuleIdent -> [(Ident,ValueInfo)] -> Doc
> ppTypes m = vcat . map (ppIDecl . mkDecl) . filter (isValue . snd)
>   where mkDecl (v,Value _ (ForAll _ ty)) =
>           IFunctionDecl undefined (qualify v) (fromQualType m ty)
>         isValue (DataConstructor _ _) = False
>         isValue (NewtypeConstructor _ _) = False
>         isValue (Value _ _) = True

\end{verbatim}
Various filename extensions.
\begin{verbatim}

> cExt = ".c"
> intfExt = ".icurry"
> litExt = ".lcurry"

\end{verbatim}
Error messages.
\begin{verbatim}

> interfaceNotFound :: ModuleIdent -> String
> interfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

> cyclicImport :: ModuleIdent -> [ModuleIdent] -> String
> cyclicImport m [] = "Recursive import for module " ++ moduleName m
> cyclicImport m ms =
>   "Cyclic import dependency between modules " ++ moduleName m ++
>     modules "" ms
>   where modules comma [m] = comma ++ " and " ++ moduleName m
>         modules _ (m:ms) = ", " ++ moduleName m ++ modules "," ms

> wrongInterface :: ModuleIdent -> ModuleIdent -> String
> wrongInterface m m' =
>   "Expected interface for " ++ show m ++ " but found " ++ show m'

\end{verbatim}
