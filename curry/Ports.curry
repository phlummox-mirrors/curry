-- $Id: Ports.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

-- Ports implementation for MCC

module Ports(Port, SP_Msg(..),
             openPort, closePort, send, doSend, choiceSPEP,
             openProcessPort, openSocketConnectPort) where

import IO
import IOExts
import Unsafe


-- Local ports

newtype Port a = Port (IORef [a])

openPort :: Port a -> [a] -> Success
openPort (Port r) ms = r =:= unsafePerformIO (newIORef ms)

closePort :: Port a -> Success
closePort (Port r) = unsafePerformIO (readIORef r) =:= []

-- NB: the message must be evaluated to normal form *before* the
--     port is updated; hence the guard expression.
send :: a -> Port a -> Success
send m (Port r) | m =:= m' =
  unsafePerformIO (do ms <- readIORef r; writeIORef r ms'; return ms) =:= m':ms'
  where m',ms' free

doSend :: a -> Port a -> IO ()
doSend m p = doSolve (send m p)


-- Stream ports

data SP_Msg = SP_Put String
            | SP_GetLine String
            | SP_GetChar Char
            | SP_EOF Bool
            | SP_Close

openProcessPort :: String -> IO (Port SP_Msg)
openProcessPort cmd =
  openProcess cmd ReadWriteMode >>= streamPort closeProcess
  where closeProcess h = pClose h >> return ()

openSocketConnectPort :: Int -> String -> IO (Port SP_Msg)
openSocketConnectPort port host =
  connectTcpSocket host port ReadWriteMode >>= streamPort hClose

streamPort :: (Handle -> IO ()) -> Handle -> IO (Port SP_Msg)
streamPort hClose h =
  do
    hSetBuffering h LineBuffering
    doSolve (openPort p ms)
    spawnConstraint (unsafePerformIO (backgroundTask ms)) (return p)
  where backgroundTask, msg eval rigid
  	-- NB Don't try to ``simplify'' backgroundTask using map, foldr,
        -- or mapIO_, since all of them are flexible functions.
	backgroundTask [] = hClose h >> return success
	backgroundTask (m:ms) = msg m >> backgroundTask ms
	msg (SP_Put s) = hPutStrLn h s
	msg (SP_GetLine s) = hGetLine h >>= doSolve . (s =:=)
	msg (SP_GetChar c) = hGetChar h >>= doSolve . (c =:=)
	msg (SP_EOF b) = hIsEOF h >>= doSolve . (b =:=)
	msg SP_Close = hClose h
        p,ms free


-- Merging

{- the following definition does not work because committed choice
   is not yet supported

choiceSPEP :: Port SP_Msg -> [a] -> Either String [a]
choiceSPEP eval choice
choiceSPEP _ ms@(_:_) = Right ms
choiceSPEP sp | send (SP_GetLine s) sp = Left s where s free

   here is a workaround using the unsafe isVar primitive
 -}

choiceSPEP :: Port SP_Msg -> [a] -> Either String [a]
choiceSPEP sp ep
  | isVar ep = chooseSP sp
  | otherwise =
      case ep of
        ms@(_:_) -> Right ms
        _ -> chooseSP sp
  where chooseSP sp | send (SP_GetLine s) sp = Left s where s free
