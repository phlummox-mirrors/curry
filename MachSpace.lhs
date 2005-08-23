% -*- LaTeX -*-
% $Id: MachSpace.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Local search spaces}
\begin{verbatim}

> module MachSpace where
> import MachTypes
> import Env
> import Combined

\end{verbatim}
The function \texttt{curContext} returns the current search context.
This is used to determine whether the machine operates in a local or
global search and in the latter case if it is executing monadic code.
\begin{verbatim}

> curContext :: Monad m => State -> m SearchContext
> curContext state = return (sc state)

\end{verbatim}
The function \texttt{curSpace} returns the current search space, the
function \texttt{setCurSpace} changes the current search space. The
predicate \texttt{isALocalSpace} tests whether the given search space
is the current local search space. Finally, \texttt{isLocalSpaceOf}
checks whether both arguments are derived from the same root space.
\begin{verbatim}

> curSpace :: Monad m => State -> m SearchSpace
> curSpace state = return (ss state)

> setCurSpace :: Monad m => SearchSpace -> State -> m State
> setCurSpace space state = return state{ ss = space }

> isALocalSpace :: RefMonad m => SearchSpace -> State -> m Bool
> isALocalSpace ptr state = ptr `isLocalSpaceOf` ss state

> isLocalSpaceOf :: RefMonad m => SearchSpace -> SearchSpace -> m Bool
> GlobalSpace `isLocalSpaceOf` GlobalSpace = return True
> GlobalSpace `isLocalSpaceOf` LocalSpace{} = return False
> LocalSpace{} `isLocalSpaceOf` GlobalSpace = return False
> LocalSpace{ root = rootRef } `isLocalSpaceOf` LocalSpace{ root = rootRef' } =
>   readRef rootRef >>= \root ->
>   readRef rootRef' >>= \root' ->
>   return (root == root')

\end{verbatim}
When \texttt{try} is invoked, the current search context must be saved
and a new search context has to be initialized. Note that we
delibaretly do not change the current search space. However, when we
restore the context we will also update the search space.
\begin{verbatim}

> pushSearchContext :: Monad m => NodePtr -> NodePtr -> State -> m State
> pushSearchContext goal var state =
>   return state{ env = emptyEnv, ds = [], rs = [], rq = [], tp = [],
>                 sc = SearchContext goal var (tid state) (ds state) (rs state)
>                                    (rq state) (tp state)
>                                    (sc state) (ss state) }

> popSearchContext :: Monad m => State -> m ((NodePtr,NodePtr),State)
> popSearchContext state =
>   case sc state of
>     IOContext -> fail "Empty search context stack"
>     GlobalContext -> fail "Empty search context stack"
>     SearchContext goal var tid ds rs rq tp sc ss ->
>       return ((goal,var),
>               state{ tid = tid, env = emptyEnv, ds = ds, rs = rs,
>                      rq = rq, tp = tp, sc = sc, ss = ss })

\end{verbatim}
A new search space is created whenever \texttt{try} is called. The new
search space will be its own root space and with the global space as
its parent. The trail and the script will be set when the search space
is saved.
\begin{verbatim}

> newSearchSpace :: RefMonad m => State -> m (SearchSpace,State)
> newSearchSpace state =
>   do
>     rootRef <- newRef undefined
>     parentRef <- newRef GlobalSpace
>     trailRef <- newRef []
>     scriptRef <- newRef []
>     activeRef <- newRef undefined
>     let newSpace = LocalSpace adr rootRef parentRef
>                               trailRef scriptRef activeRef
>     writeRef rootRef newSpace
>     writeRef activeRef newSpace
>     return (newSpace,state{ hp = adr + 1 })
>   where adr = hp state

\end{verbatim}
A search space will be saved when the encapsulated search returns with
a solved goal or with a list of alternative continuations. In this
case the trail is copied into the search space. Note that the trail
pointer of the abstract machine is reset. Also note that the script is
not computed. It will be computed in the function \texttt{actBindings}
when the active search space really changes.
\begin{verbatim}

> saveSearchSpace :: RefMonad m => State -> m (SearchSpace,State)
> saveSearchSpace state = save (ss state)
>   where save GlobalSpace = fail "Cannot save the global search space"
>         save space =
>           do
>             writeRef (trail space) (tp state)
>             readRef (root space) >>= flip writeRef space . active
>             return (space,state{ ss = GlobalSpace, tp = [] })

\end{verbatim}
When the encapsulated search fails, the current search space is simply
discarded and the bindings recorded on the trail are undone.
\begin{verbatim}

> discardSearchSpace :: RefMonad m => State -> m State
> discardSearchSpace state =
>   do
>     mapM_ undoBinding (tp state)
>     return state{ ss = GlobalSpace, tp = [] }
>   where undoBinding (NodeBinding (Ptr _ ref) node) = writeRef ref node
>         undoBinding (ThreadState (ThreadPtr rthd) thd) = writeRef rthd thd

\end{verbatim}
When a search space is restored its bindings are activated, again. In
addition, the current search space becomes a child of the restored
search space. However, this is possible only if the current search
space is a root space. The function \texttt{isRootSpace} can be used
to check this condition. Note that the global search space is not a
root space. Also note that the active search space pointer of the
current space becomes invalid as soon as it becomes a child of the
restored space, because we must maintain only a single active pointer
for each hierarchy of spaces.
\begin{verbatim}

> isRootSpace :: RefMonad m => SearchSpace -> m Bool
> isRootSpace GlobalSpace = return False
> isRootSpace space@LocalSpace{ parent = parentRef } =
>   readRef parentRef >>= return . (GlobalSpace ==)

> restoreSearchSpace :: RefMonad m => SearchSpace -> State -> m State
> restoreSearchSpace GlobalSpace state =
>   fail "Cannot restore global search space"
> restoreSearchSpace space state = restore (ss state)
>   where restore GlobalSpace =
>           fail "Cannot restore search space into global space"
>         restore LocalSpace{ root = rootRef, parent = parentRef,
>                             active = activeRef } =
>           readRef parentRef >>= return . (GlobalSpace ==) >>= \so ->
>           if so then
>             do
>               actBindings space
>               readRef (root space) >>= writeRef rootRef
>               writeRef parentRef space
>               writeRef activeRef undefined
>               return state
>           else
>             fail "Cannot restore search space into non-root space"

\end{verbatim}
If we are restoring a search space, its bindings may not be in
effect. In that case we will have to undo the bindings made the search
space whose bindings are in effect and of all its parents and the redo
the bindings of the current search space (and all its parents) using
the script. In fact we do not have to move up the root but only up to
the closest common ancestor.\footnote{The same optimization is also
implemented in Amoz.} While undoing the effective bindings on the
trail we also have to initialize the script, if it is not already
initialized.\footnote{We just consider an empty script to be uninitialized
here.} As in our implementation not only single assignment variables
are updated we must be careful about the order in which the bindings
are undone and applied, otherwise wrong bindings might be restored. To
identify a search space -- which does not support equality because its
trail component does not -- we use the mutable variable pointing to
the binding vector.
\begin{verbatim}

> actBindings :: RefMonad m => SearchSpace -> m ()
> actBindings GlobalSpace = fail "Attempt to change to the global space"
> actBindings space =
>   readRef (root space) >>= changeBindings space
>   where changeBindings space GlobalSpace = fail "Invalid root space"
>         changeBindings space LocalSpace{ active = activeRef } =
>           do
>             readRef activeRef >>= undoBindings
>             redoBindings space
>             writeRef activeRef space
>         undoBindings GlobalSpace = return ()
>         undoBindings LocalSpace{ parent = parentRef, trail = trailRef,
>                                  script = scriptRef } =
>           do
>             trail <- readRef trailRef
>             script <- readRef scriptRef
>             if null script && not (null trail) then
>                 mapM exchangeBinding trail >>= writeRef scriptRef . reverse
>               else
>                 mapM_ undoBinding trail
>             readRef parentRef >>= undoBindings
>         redoBindings GlobalSpace = return ()
>         redoBindings LocalSpace{ parent = parentRef, script = scriptRef } =
>           do
>             readRef parentRef >>= redoBindings
>             readRef scriptRef >>= mapM_ redoBinding
>         undoBinding (NodeBinding (Ptr _ ref) node) = writeRef ref node
>         undoBinding (ThreadState (ThreadPtr rthd) thd) = writeRef rthd thd
>         redoBinding = undoBinding
>         exchangeBinding (NodeBinding (Ptr adr ref) node) =
>           do
>             node' <- readRef ref
>             writeRef ref node
>             return (NodeBinding (Ptr adr ref) node')
>         exchangeBinding (ThreadState (ThreadPtr rthd) thd) =
>           do
>             thd' <- readRef rthd
>             writeRef rthd thd
>             return (ThreadState (ThreadPtr rthd) thd')

\end{verbatim}
\ToDo{Implement the closest common ancestor optimization.}
