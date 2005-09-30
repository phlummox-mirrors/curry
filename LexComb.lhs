% -*- LaTeX -*-
% $Id: LexComb.lhs 1777 2005-09-30 14:56:48Z wlux $
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
> import Position
> import Error
> import Char
> import Numeric

> infixl 1 `thenP`, `thenP_`

> type Indent = Int
> type Context = [Indent]
> type P a = Position -> String -> Bool -> Context -> Error a

> parse :: P a -> FilePath -> String -> Error a
> parse p fn s = p (first fn) s False []

\end{verbatim}
Monad functions for the lexer.
\begin{verbatim}

> returnP :: a -> P a
> returnP x _ _ _ _ = Ok x

> thenP :: P a -> (a -> P b) -> P b
> thenP lex k pos s bol ctxt = lex pos s bol ctxt >>= \x -> k x pos s bol ctxt

> thenP_ :: P a -> P b -> P b
> p1 `thenP_` p2 = p1 `thenP` \_ -> p2

> failP :: Position -> String -> P a
> failP pos msg _ _ _ _ = Error (parseError pos msg)

> closeP0 :: P a -> P (P a)
> closeP0 lex pos s bol ctxt = Ok (\_ _ _ _ -> lex pos s bol ctxt)

> closeP1 :: (a -> P b) -> P (a -> P b)
> closeP1 f pos s bol ctxt = Ok (\x _ _ _ _ -> f x pos s bol ctxt)

> parseError :: Position -> String -> String
> parseError p what = show p ++ ": " ++ what

\end{verbatim}
Combinators that handle layout.
\begin{verbatim}

> pushContext :: Int -> P a -> P a
> pushContext col cont pos s bol ctxt = cont pos s bol (col:ctxt)

> popContext :: P a -> P a
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
