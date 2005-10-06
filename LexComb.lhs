% -*- LaTeX -*-
% $Id: LexComb.lhs 1782 2005-10-06 13:45:22Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{LexComb.lhs}
\section{Lexing combinators}
The module \texttt{LexComb} provides the basic types and combinators
to implement the lexers. The combinators use continuation passing code
in a monadic style. The first argument of the continuation function is
the string to be parsed, the second is the current position, and the
third is a flag which signals the lexer that it is lexing the
beginning of a line and therefore has to check for layout tokens. The
fourth argument is a stack of indentations that is used to handle
nested layout groups.
\begin{verbatim}

> module LexComb where
> import Prelude hiding(lex)
> import Position
> import Error
> import Char
> import Numeric

> infixl 1 `thenL`, `thenL_`

> type Indent = Int
> type Context = [Indent]
> type L a = Position -> String -> Bool -> Context -> Error a

> lex :: L a -> FilePath -> String -> Error a
> lex p fn s = p (first fn) s False []

\end{verbatim}
Monad functions for the lexer.
\begin{verbatim}

> returnL :: a -> L a
> returnL x _ _ _ _ = Ok x

> thenL :: L a -> (a -> L b) -> L b
> thenL lex k pos s bol ctxt = lex pos s bol ctxt >>= \x -> k x pos s bol ctxt

> thenL_ :: L a -> L b -> L b
> p1 `thenL_` p2 = p1 `thenL` \_ -> p2

> failL :: Position -> String -> L a
> failL pos msg _ _ _ _ = Error (lexError pos msg)

> closeL0 :: L a -> L (L a)
> closeL0 lex pos s bol ctxt = Ok (\_ _ _ _ -> lex pos s bol ctxt)

> closeL1 :: (a -> L b) -> L (a -> L b)
> closeL1 f pos s bol ctxt = Ok (\x _ _ _ _ -> f x pos s bol ctxt)

> lexError :: Position -> String -> String
> lexError p what = show p ++ ": " ++ what

\end{verbatim}
Combinators that handle layout.
\begin{verbatim}

> pushContext :: Int -> L a -> L a
> pushContext col cont pos s bol ctxt = cont pos s bol (col:ctxt)

> popContext :: L a -> L a
> popContext cont pos s bol (_:ctxt) = cont pos s bol ctxt
> popContext cont pos s bol [] = error "internal error: popContext"

\end{verbatim}
Conversions from strings into numbers.
\begin{verbatim}

> convertSignedIntegral :: Num a => a -> String -> a
> convertSignedIntegral b ('+':s) = convertIntegral b s
> convertSignedIntegral b ('-':s) = - convertIntegral b s
> convertSignedIntegral b s = convertIntegral b s

> convertIntegral :: Num a => a -> String -> a
> convertIntegral b = foldl op 0
>   where m `op` n = b * m + fromIntegral (digitToInt n)

> convertSignedFloating :: RealFloat a => String -> String -> Int -> a
> convertSignedFloating ('+':m) f e = convertFloating m f e
> convertSignedFloating ('-':m) f e = - convertFloating m f e
> convertSignedFloating m f e = convertFloating m f e

> convertFloating :: RealFloat a => String -> String -> Int -> a
> convertFloating m f e =
>   case readFloat (m ++ f ++ 'e' : show (e - length f)) of
>     [(f,"")] -> f
>     _ -> error "internal error: invalid string (convertFloating)"

\end{verbatim}
