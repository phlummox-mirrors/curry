% -*- LaTeX -*-
% $Id: Modules.lhs 2461 2007-09-07 08:55:15Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
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
> import KindCheck(kindCheck,kindCheckGoal)
> import TypeCheck(typeCheck,typeCheckGoal)
> import CaseCheck(caseCheck,caseCheckGoal)
> import UnusedCheck(unusedCheck,unusedCheckGoal)
> import ShadowCheck(shadowCheck,shadowCheckGoal)
> import OverlapCheck(overlapCheck,overlapCheckGoal)
> import IntfSyntaxCheck(intfSyntaxCheck)
> import IntfCheck(intfCheck)
> import IntfEquiv(fixInterface,intfEquiv)
> import Imports(importInterface,importInterfaceIntf,importUnifyData)
> import Exports(exportInterface)
> import Trust(trustEnv)
> import Qual(Qual(..))
> import Desugar(desugar,goalModule)
> import Simplify(simplify)
> import Unlambda(unlambda)
> import Lift(lift)
> import qualified IL
> import ILTrans(ilTrans,ilTransIntf)
> import ILLift(liftProg)
> import DTransform(dTransform,dAddMain)
> import ILCompile(camCompile,camCompileData,fun)
> import qualified CamPP(ppModule)
> import CGen(genMain,genModule)
> import CCode(CFile,mergeCFile)
> import CPretty(ppCFile)
> import CurryPP(ppModule,ppInterface,ppIDecl,ppGoal)
> import qualified ILPP(ppModule)
> import Options(Options(..),CaseMode(..),Warn(..),Dump(..))
> import CurrySyntax
> import Env
> import TopEnv
> import Combined
> import Error
> import IO
> import List
> import Maybe
> import Monad
> import PathUtils
> import Position
> import PredefIdent
> import Pretty
> import Types
> import TypeTrans
> import Typing
> import Utils

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
>     (mEnv,pEnv,tcEnv,tyEnv,m) <- loadModule paths dbg cm ws fn
>     let (tyEnv',trEnv,m',dumps) = transModule dbg tr tcEnv tyEnv m
>     liftErr $ mapM_ (doDump opts) dumps
>     let intf = exportInterface m pEnv tcEnv tyEnv'
>     liftErr $ unless (noInterface opts) (updateInterface fn intf)
>     let (il,dumps) = ilTransModule split dbg tyEnv' trEnv m'
>     liftErr $ mapM_ (doDump opts) dumps
>     let (ccode,dumps) = genCodeModule (bindModule intf mEnv) il
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeCode (output opts) fn ccode
>   where paths = importPath opts
>         split = splitCode opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> loadModule :: [FilePath] -> Bool -> CaseMode -> [Warn] -> FilePath
>            -> ErrorT IO (ModuleEnv,PEnv,TCEnv,ValueEnv,Module Type)
> loadModule paths debug caseMode warn fn =
>   do
>     Module m es is ds <- liftErr (readFile fn) >>= okM . parseModule fn
>     let is' = importPrelude debug fn m is
>     mEnv <- loadInterfaces paths [] emptyEnv m (modules is')
>     okM $ checkInterfaces mEnv
>     (pEnv,tcEnv,tyEnv,m') <- okM $ checkModule mEnv (Module m es is' ds)
>     liftErr $ mapM_ putErrLn $ warnModule caseMode warn m'
>     return (mEnv,pEnv,tcEnv,tyEnv,m')
>   where modules is = [P p m | ImportDecl p m _ _ _ <- is]

> parseModule :: FilePath -> String -> Error (Module ())
> parseModule fn s = unlitLiterate fn s >>= parseSource fn

> checkModule :: ModuleEnv -> Module a
>             -> Error (PEnv,TCEnv,ValueEnv,Module Type)
> checkModule mEnv (Module m es is ds) =
>   do
>     (pEnv,tcEnv,tyEnv) <- importModules mEnv' is
>     (tEnv,ds') <- typeSyntaxCheck m tcEnv ds
>     (vEnv,ds'') <- syntaxCheck m tyEnv ds'
>     es' <- checkExports m is tEnv vEnv es
>     (pEnv',ds''') <- precCheck m pEnv $ rename ds''
>     tcEnv' <- kindCheck m tcEnv ds'''
>     (tyEnv',ds'''') <- typeCheck m tcEnv' tyEnv ds'''
>     let (pEnv'',tcEnv'',tyEnv'') = qualifyEnv mEnv' m pEnv' tcEnv' tyEnv'
>     return (pEnv'',tcEnv'',tyEnv'',
>             Module m (Just es') is (qual tyEnv' ds''''))
>   where mEnv' = sanitizeInterfaces m mEnv

> warnModule :: CaseMode -> [Warn] -> Module a -> [String]
> warnModule caseMode warn m =
>   caseCheck caseMode m ++ unusedCheck warn m ++
>   shadowCheck warn m ++ overlapCheck warn m

> transModule :: Bool -> Trust -> TCEnv -> ValueEnv -> Module Type
>             -> (ValueEnv,TrustEnv,Module Type,[(Dump,Doc)])
> transModule debug tr tcEnv tyEnv m = (tyEnv''',trEnv,nolambda,dumps)
>   where trEnv = if debug then trustEnv tr m else emptyEnv
>         (desugared,tyEnv') = desugar tcEnv tyEnv m
>         (simplified,tyEnv'') = simplify tyEnv' trEnv desugared
>         (nolambda,tyEnv''') = unlambda tyEnv'' simplified
>         dumps =
>           [(DumpRenamed,ppModule m),
>            (DumpTypes,ppTypes tcEnv (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpSimplified,ppModule simplified),
>            (DumpUnlambda,ppModule nolambda)]

> ilTransModule :: Bool -> Bool -> ValueEnv -> TrustEnv -> Module Type
>               -> (Either IL.Module [IL.Module],[(Dump,Doc)])
> ilTransModule False debug tyEnv trEnv m = (Left il,dumps)
>   where (il,dumps) = ilTransModule1 id debug tyEnv trEnv m
> ilTransModule True debug tyEnv trEnv m = (Right il,concat (transpose dumps))
>   where (il,dumps) =
>           unzip $ map (ilTransModule1 id debug tyEnv trEnv) (splitModule m)

> ilTransModule1 :: (IL.Module -> IL.Module) -> Bool -> ValueEnv -> TrustEnv
>                -> Module Type -> (IL.Module,[(Dump,Doc)])
> ilTransModule1 debugAddMain debug tyEnv trEnv m = (ilDbg,dumps)
>   where (lifted,tyEnv',trEnv') = lift tyEnv trEnv m
>         il = ilTrans tyEnv' lifted
>         ilDbg
>           | debug = debugAddMain (dTransform (trustedFun trEnv') il)
>           | otherwise = il
>         dumps =
>           [(DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug]

> genCodeModule :: ModuleEnv -> Either IL.Module [IL.Module]
>               -> (Either CFile [CFile],[(Dump,Doc)])
> genCodeModule mEnv (Left il) = (Left ccode,dumps)
>   where (ccode,dumps) = genCode (ilImports mEnv il) il
> genCodeModule mEnv (Right il) = (Right ccode,concat (transpose dumps))
>   where IL.Module m is ds = mergeILModules il
>         (ccode,dumps) =
>           unzip $ map (genCode (ilImports mEnv (IL.Module m is ds) ++ ds)) il

> genCode :: [IL.Decl] -> IL.Module -> (CFile,[(Dump,Doc)])
> genCode ds il = (ccode,dumps)
>   where ilNormal = liftProg il
>         cam = camCompile ilNormal
>         imports = camCompileData ds
>         ccode = genModule imports cam
>         dumps =
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

> qualifyEnv :: ModuleEnv -> ModuleIdent -> PEnv -> TCEnv -> ValueEnv
>            -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv mEnv m pEnv tcEnv tyEnv =
>   (foldr (uncurry (globalBindTopEnv m)) pEnv' (localBindings pEnv),
>    foldr (uncurry (globalBindTopEnv m)) tcEnv' (localBindings tcEnv),
>    foldr (uncurry (bindTopEnv m)) tyEnv' (localBindings tyEnv))
>   where (pEnv',tcEnv',tyEnv') =
>           foldl importInterfaceIntf initEnvs (map snd (envToList mEnv))

> splitModule :: Module a -> [Module a]
> splitModule (Module m es is ds) = [Module m es is [d] | d <- ds, isCodeDecl d]
>   where isCodeDecl (DataDecl _ _ _ cs) = not (null cs)
>         isCodeDecl (NewtypeDecl _ _ _ _) = True
>         isCodeDecl (TypeDecl _ _ _ _) = False
>         isCodeDecl (BlockDecl d) = isValueDecl d

> mergeILModules :: [IL.Module] -> IL.Module
> mergeILModules ms = IL.Module m (concat iss) (concat dss)
>   where IL.Module m _ _ : _ = ms
>         (iss,dss) = unzip [(is,ds) | IL.Module _ is ds <- ms]

> ilImports :: ModuleEnv -> IL.Module -> [IL.Decl]
> ilImports mEnv (IL.Module _ is _) =
>   concat [ilTransIntf i | (m,i) <- envToList mEnv, m `elem` is]

> trustedFun :: TrustEnv -> QualIdent -> Bool
> trustedFun trEnv f = maybe True (Trust ==) (lookupEnv (unqualify f) trEnv)

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
A goal is compiled with respect to the interface of a given module. If
no module is specified, the Curry \texttt{Prelude} is used. All
entities exported from the main module and the \texttt{Prelude} are in
scope with their unqualified names. In addition, the entities exported
from all loaded interfaces are in scope with their qualified names.
\begin{verbatim}

> data Task = Eval | Type

> compileGoal :: Options -> Maybe String -> [FilePath] -> ErrorT IO ()
> compileGoal opts g fns =
>   do
>     (mEnv,tcEnv,tyEnv,g') <- loadGoal Eval paths dbg cm ws m g fns
>     let (vs,m',tyEnv') = goalModule dbg tyEnv m mainId g'
>     let (tyEnv'',trEnv,m'',dumps) = transModule dbg tr tcEnv tyEnv' m'
>     liftErr $ mapM_ (doDump opts) dumps
>     let (il,dumps) = ilTransModule1 (dAddMain mainId) dbg tyEnv'' trEnv m''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (ccode,dumps) = genCodeGoal mEnv (qualifyWith m mainId) vs il
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeGoalCode (output opts) ccode
>   where m = mkMIdent []
>         paths = importPath opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> typeGoal :: Options -> String -> [FilePath] -> ErrorT IO ()
> typeGoal opts g fns =
>   do
>     (_,tcEnv,_,Goal _ e _) <-
>       loadGoal Type paths False cm ws (mkMIdent []) (Just g) fns
>     liftErr $ print (ppType tcEnv (typeOf e))
>   where paths = importPath opts
>         cm = caseMode opts
>         ws = warn opts

> loadGoal :: Task -> [FilePath] -> Bool -> CaseMode -> [Warn]
>          -> ModuleIdent -> Maybe String -> [FilePath]
>          -> ErrorT IO (ModuleEnv,TCEnv,ValueEnv,Goal Type)
> loadGoal task paths debug caseMode warn m g fns =
>   do
>     (mEnv,m') <- loadGoalModules paths debug fns
>     (tcEnv,tyEnv,g') <-
>       okM $ maybe (return (mainGoal m')) parseGoal g >>=
>             checkGoal task mEnv m (nub [m',preludeMIdent])
>     liftErr $ mapM_ putErrLn $ warnGoal caseMode warn m g'
>     return (mEnv,tcEnv,tyEnv,g')
>   where mainGoal m = Goal (first "") (Variable () (qualifyWith m mainId)) []

> loadGoalModules :: [FilePath] -> Bool -> [FilePath]
>                 -> ErrorT IO (ModuleEnv,ModuleIdent)
> loadGoalModules paths debug fns =
>   do
>     mEnv <- foldM (loadInterface paths []) emptyEnv ms
>     (mEnv',ms') <- mapAccumM (loadGoalInterface paths) mEnv fns
>     okM $ checkInterfaces mEnv'
>     return (mEnv',last (preludeMIdent:ms'))
>   where ms = map (P (first "")) (preludeMIdent : [debugPreludeMIdent | debug])

> loadGoalInterface :: [FilePath] -> ModuleEnv -> FilePath
>                   -> ErrorT IO (ModuleEnv,ModuleIdent)
> loadGoalInterface paths mEnv fn
>   | extension fn `elem` [srcExt,litExt,intfExt] || pathSep `elem` fn =
>       compileInterface paths [] mEnv (interfaceName fn)
>   | otherwise =
>       do
>         mEnv' <- loadInterface paths [] mEnv (P (first "") m)
>         return (mEnv',m)
>   where m = mkMIdent (components ('.':fn))
>         components [] = []
>         components (_:cs) =
>           case break ('.' ==) cs of
>             (cs',cs'') -> cs' : components cs''

> checkGoal :: Task -> ModuleEnv -> ModuleIdent -> [ModuleIdent] -> Goal a
>           -> Error (TCEnv,ValueEnv,Goal Type)
> checkGoal task mEnv m ms g =
>   do
>     let (pEnv,tcEnv,tyEnv) = importInterfaces mEnv ms
>     g' <- typeSyntaxCheckGoal tcEnv g >>=
>           syntaxCheckGoal tyEnv >>=
>           precCheckGoal m pEnv . renameGoal
>     (tyEnv',g'') <- kindCheckGoal tcEnv g' >>
>                     typeCheckGoal m tcEnv tyEnv g'
>     return (qualifyGoal task mEnv m pEnv tcEnv tyEnv' g'')

> qualifyGoal :: Task -> ModuleEnv -> ModuleIdent -> PEnv -> TCEnv -> ValueEnv
>             -> Goal a -> (TCEnv,ValueEnv,Goal a)
> qualifyGoal Eval mEnv m pEnv tcEnv tyEnv g = (tcEnv',tyEnv',qual tyEnv g)
>   where (_,tcEnv',tyEnv') = qualifyEnv mEnv m pEnv tcEnv tyEnv
> qualifyGoal Type _ _ _ tcEnv tyEnv g = (tcEnv,tyEnv,g)

> warnGoal :: CaseMode -> [Warn] -> ModuleIdent -> Goal a -> [String]
> warnGoal caseMode warn m g =
>   caseCheckGoal caseMode g ++ unusedCheckGoal warn m g ++
>   shadowCheckGoal warn g ++ overlapCheckGoal warn g

> genCodeGoal :: ModuleEnv -> QualIdent -> Maybe [Ident] -> IL.Module
>             -> (CFile,[(Dump,Doc)])
> genCodeGoal mEnv qGoalId vs il = (mergeCFile ccode ccode',dumps)
>   where (ccode,dumps) = genCode (ilImports mEnv il) il
>         ccode' = genMain (fun qGoalId) (fmap (map name) vs)

\end{verbatim}
The function \texttt{importModules} brings the declarations of all
imported modules into scope in the current module.
\begin{verbatim}

> importModules :: ModuleEnv -> [ImportDecl] -> Error (PEnv,TCEnv,ValueEnv)
> importModules mEnv ds =
>   do
>     ds' <- mapE checkImportDecl ds
>     let (pEnv,tcEnv,tyEnv) = foldl importModule initEnvs ds'
>     return (pEnv,importUnifyData tcEnv,tyEnv)
>   where checkImportDecl (ImportDecl p m q asM is) =
>           liftE (ImportDecl p m q asM)
>                 (checkImports (moduleInterface m mEnv) is)
>         importModule envs (ImportDecl _ m q asM is) =
>           importInterface (fromMaybe m asM) q is envs (moduleInterface m mEnv)

> moduleInterface :: ModuleIdent -> ModuleEnv -> Interface
> moduleInterface m mEnv =
>   fromMaybe (internalError "moduleInterface") (lookupEnv m mEnv)

> initEnvs :: (PEnv,TCEnv,ValueEnv)
> initEnvs = (initPEnv,initTCEnv,initDCEnv)

\end{verbatim}
The function \texttt{importInterfaces} brings the declarations of all
loaded modules into scope with their qualified names and in addition
brings the declarations of the specified modules into scope with their
unqualified names too.
\begin{verbatim}

> importInterfaces :: ModuleEnv -> [ModuleIdent] -> (PEnv,TCEnv,ValueEnv)
> importInterfaces mEnv ms = (pEnv,importUnifyData tcEnv,tyEnv)
>   where (pEnv,tcEnv,tyEnv) =
>           foldl (uncurry . importModule) initEnvs (envToList mEnv)
>         importModule envs m = importInterface m (m `notElem` ms) Nothing envs

\end{verbatim}
When mutually recursive modules are compiled, it may be possible that
the imported interfaces include entities that are supposed to be
defined in the current module. These entities must not be imported
into the current module in any way because they might be in conflict
with the actual definitions in the current module.
\begin{verbatim}

> sanitizeInterfaces :: ModuleIdent -> ModuleEnv -> ModuleEnv
> sanitizeInterfaces m mEnv = fmap (sanitizeInterface m) (unbindModule m mEnv)

> sanitizeInterface :: ModuleIdent -> Interface -> Interface
> sanitizeInterface m (Interface m' is' ds') =
>   Interface m' is' (filter ((Just m /=) . fst . splitQualIdent . entity) ds')
>   where entity (IInfixDecl _ _ _ op) = op
>         entity (HidingDataDecl _ tc _) = tc
>         entity (IDataDecl _ tc _ _) = tc
>         entity (INewtypeDecl _ tc _ _) = tc
>         entity (ITypeDecl _ tc _ _) = tc
>         entity (IFunctionDecl _ f _ _) = f

\end{verbatim}
The prelude is imported implicitly into every module that does not
import the prelude explicitly with an import declaration. Obviously,
no import declaration is added to the prelude itself. Furthermore, the
module \texttt{DebugPrelude} is imported into every module when it is
compiled for debugging. However, none of its entities are brought into
scope because the debugging transformation is applied to the
intermediate language.
\begin{verbatim}

> importPrelude :: Bool -> FilePath -> ModuleIdent
>               -> [ImportDecl] -> [ImportDecl]
> importPrelude debug fn m is =
>   imp True preludeMIdent True ++ imp debug debugPreludeMIdent False ++ is
>   where p = first fn
>         ms = m : [m | ImportDecl _ m _ _ _ <- is]
>         imp cond m all = [importDecl p m all | cond && m `notElem` ms]

> importDecl :: Position -> ModuleIdent -> Bool -> ImportDecl
> importDecl p m all =
>   ImportDecl p m False Nothing
>              (if all then Nothing else Just (Importing p []))

\end{verbatim}
If an import declaration for a module is found, the compiler loads the
module's interface unless a load is already pending. Such is possible
in the case of cyclic module dependencies, which are accepted as an
extension to the Curry language. An error is reported only if a module
contains an import declaration directly importing itself.
\begin{verbatim}

> loadInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv
>                -> ModuleIdent -> [P ModuleIdent] -> ErrorT IO ModuleEnv
> loadInterfaces paths ctxt mEnv m ms =
>   do
>     okM $ sequenceE_ [errorAt p (cyclicImport m) | P p m' <- ms, m == m']
>     foldM (loadInterface paths ctxt) mEnv ms

> loadInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> P ModuleIdent
>               -> ErrorT IO ModuleEnv
> loadInterface paths ctxt mEnv (P p m)
>   | m `elem` ctxt || isJust (lookupEnv m mEnv) = return mEnv
>   | otherwise =
>       liftErr (lookupInterface paths m) >>=
>       maybe (errorAt p (interfaceNotFound m))
>             (compileModuleInterface paths ctxt mEnv m)

> compileModuleInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv
>                        -> ModuleIdent -> FilePath -> ErrorT IO ModuleEnv
> compileModuleInterface paths ctxt mEnv m fn =
>   do
>     (mEnv',m') <- compileInterface paths ctxt mEnv fn
>     unless (m == m') (errorAt (first fn) (wrongInterface m m'))
>     return mEnv'

\end{verbatim}
After parsing an interface, all of its imported interfaces are
recursively loaded and entered into the module environment. In
addition, the compiler applies syntax checking to the interface, which
is possible because interface files are self-contained.

\ToDo{Avoid recursive loading of imported interfaces. All information
that is needed for compiling a module is present in the interfaces
that are imported directly from that module.}
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv
>                  -> FilePath -> ErrorT IO (ModuleEnv,ModuleIdent)
> compileInterface paths ctxt mEnv fn =
>   do
>     Interface m is ds <- liftErr (readFile fn) >>= okM . parseInterface fn
>     mEnv' <- loadInterfaces paths (m:ctxt) mEnv m (modules is)
>     ds' <- okM $ intfSyntaxCheck ds
>     return (bindModule (Interface m is ds') mEnv',m)
>   where modules is = [P p m | IImportDecl p m <- is]

\end{verbatim}
After all interface files have been loaded, the compiler checks that
re-exported definitions in the interfaces are compatible with their
original definitions in order to ensure that the set of loaded
interfaces is consistent.
\begin{verbatim}

> checkInterfaces :: ModuleEnv -> Error ()
> checkInterfaces mEnv = mapE_ (checkInterface mEnv . snd) (envToList mEnv)

> checkInterface :: ModuleEnv -> Interface -> Error ()
> checkInterface mEnv (Interface m is ds) = intfCheck m pEnv tcEnv tyEnv ds
>   where (pEnv,tcEnv,tyEnv) = foldl importModule initEnvs is
>         importModule envs (IImportDecl _ m) =
>           importInterfaceIntf envs (moduleInterface m mEnv)

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
>   where ifn = interfaceName sfn

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

> interfaceName :: FilePath -> FilePath
> interfaceName fn = rootname fn ++ intfExt

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
> dumpHeader DumpUnlambda = "Source code after naming lambdas"
> dumpHeader DumpLifted = "Source code after lifting"
> dumpHeader DumpIL = "Intermediate code"
> dumpHeader DumpTransformed = "Transformed code" 
> dumpHeader DumpNormalized = "Intermediate code after normalization"
> dumpHeader DumpCam = "Abstract machine code"

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: TCEnv -> [(Ident,ValueInfo)] -> Doc
> ppTypes tcEnv = vcat . map ppInfo
>   where ppInfo (c,DataConstructor _ _ ty) =
>           ppIDecl (mkDecl c ty) <+> text "-- data constructor"
>         ppInfo (c,NewtypeConstructor _ ty) =
>           ppIDecl (mkDecl c ty) <+> text "-- newtype constructor"
>         ppInfo (x,Value _ _ ty) = ppIDecl (mkDecl x ty)
>         mkDecl f ty =
>           IFunctionDecl undefined (qualify f) Nothing
>                         (fromType tcEnv nameSupply (rawType ty))

\end{verbatim}
Various file name extensions.
\begin{verbatim}

> cExt = ".c"
> srcExt = ".curry"
> litExt = ".lcurry"
> intfExt = ".icurry"

\end{verbatim}
Auxiliary functions. Unfortunately, hbc's \texttt{IO} module lacks a
definition of \texttt{hPutStrLn}.
\begin{verbatim}

> putErr :: String -> IO ()
> putErr = hPutStr stderr

> putErrLn :: String -> IO ()
> putErrLn s = putErr (unlines [s])

\end{verbatim}
Error messages.
\begin{verbatim}

> interfaceNotFound :: ModuleIdent -> String
> interfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

> cyclicImport :: ModuleIdent -> String
> cyclicImport m = "Module " ++ moduleName m ++ " imports itself"

> wrongInterface :: ModuleIdent -> ModuleIdent -> String
> wrongInterface m m' =
>   "Expected interface for " ++ show m ++ " but found " ++ show m'

\end{verbatim}
