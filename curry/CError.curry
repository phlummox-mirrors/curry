-- $Id: CError.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module CError(Errno(..), eOK, e2BIG, eACCES, eADDRINUSE, eADDRNOTAVAIL,
              eADV, eAFNOSUPPORT, eAGAIN, eALREADY, eBADF, eBADMSG, eBADRPC,
              eBUSY, eCHILD, eCOMM, eCONNABORTED, eCONNREFUSED, eCONNRESET,
              eDEADLK, eDESTADDRREQ, eDIRTY, eDOM, eDQUOT, eEXIST, eFAULT,
              eFBIG, eFTYPE, eHOSTDOWN, eHOSTUNREACH, eIDRM, eILSEQ,
              eINPROGRESS, eINTR, eINVAL, eIO, eISCONN, eISDIR, eLOOP,
              eMFILE, eMLINK, eMSGSIZE, eMULTIHOP, eNAMETOOLONG, eNETDOWN,
              eNETRESET, eNETUNREACH, eNFILE, eNOBUFS, eNODATA, eNODEV,
              eNOENT, eNOEXEC, eNOLCK, eNOLINK, eNOMEM, eNOMSG, eNONET,
              eNOPROTOOPT, eNOSPC, eNOSR, eNOSTR, eNOSYS, eNOTBLK, eNOTCONN,
              eNOTDIR, eNOTEMPTY, eNOTSOCK, eNOTTY, eNXIO, eOPNOTSUPP,
              ePERM, ePFNOSUPPORT, ePIPE, ePROCLIM, ePROCUNAVAIL,
              ePROGMISMATCH, ePROGUNAVAIL, ePROTO, ePROTONOSUPPORT,
              ePROTOTYPE, eRANGE, eREMCHG, eREMOTE, eROFS, eRPCMISMATCH,
              eRREMOTE, eSHUTDOWN, eSOCKTNOSUPPORT, eSPIPE, eSRCH, eSRMNT,
              eSTALE, eTIME, eTIMEDOUT, eTOOMANYREFS, eTXTBSY, eUSERS,
              eWOULDBLOCK, eXDEV, isValidErrno, 
              getErrno, resetErrno, errnoToIOError,
              throwErrno, throwErrnoIf, throwErrnoIf_,
              throwErrnoIfRetry, throwErrnoIfRetry_,
              throwErrnoIfMinus1, throwErrnoIfMinus1_,
              throwErrnoIfMinus1Retry, throwErrnoIfMinus1Retry_,
              throwErrnoIfNull, throwErrnoIfNullRetry) where
import Ptr
import CTypes
import CString
import IO
import Unsafe

newtype Errno = Errno CInt

eOK = Errno 0
e2BIG = Errno e2BIG
  where foreign import ccall "prim_errno.h" e2BIG :: Int
eACCES = Errno eACCES
  where foreign import ccall "prim_errno.h" eACCES :: Int
eADDRINUSE = Errno eADDRINUSE
  where foreign import ccall "prim_errno.h" eADDRINUSE :: Int
eADDRNOTAVAIL = Errno eADDRNOTAVAIL
  where foreign import ccall "prim_errno.h" eADDRNOTAVAIL :: Int
eADV = Errno eADV
  where foreign import ccall "prim_errno.h" eADV :: Int
eAFNOSUPPORT = Errno eAFNOSUPPORT
  where foreign import ccall "prim_errno.h" eAFNOSUPPORT :: Int
eAGAIN = Errno eAGAIN
  where foreign import ccall "prim_errno.h" eAGAIN :: Int
eALREADY = Errno eALREADY
  where foreign import ccall "prim_errno.h" eALREADY :: Int
eBADF = Errno eBADF
  where foreign import ccall "prim_errno.h" eBADF :: Int
eBADMSG = Errno eBADMSG
  where foreign import ccall "prim_errno.h" eBADMSG :: Int
eBADRPC = Errno eBADRPC
  where foreign import ccall "prim_errno.h" eBADRPC :: Int
eBUSY = Errno eBUSY
  where foreign import ccall "prim_errno.h" eBUSY :: Int
eCHILD = Errno eCHILD
  where foreign import ccall "prim_errno.h" eCHILD :: Int
eCOMM = Errno eCOMM
  where foreign import ccall "prim_errno.h" eCOMM :: Int
eCONNABORTED = Errno eCONNABORTED
  where foreign import ccall "prim_errno.h" eCONNABORTED :: Int
eCONNREFUSED = Errno eCONNREFUSED
  where foreign import ccall "prim_errno.h" eCONNREFUSED :: Int
eCONNRESET = Errno eCONNRESET
  where foreign import ccall "prim_errno.h" eCONNRESET :: Int
eDEADLK = Errno eDEADLK
  where foreign import ccall "prim_errno.h" eDEADLK :: Int
eDESTADDRREQ = Errno eDESTADDRREQ
  where foreign import ccall "prim_errno.h" eDESTADDRREQ :: Int
eDIRTY = Errno eDIRTY
  where foreign import ccall "prim_errno.h" eDIRTY :: Int
eDOM = Errno eDOM
  where foreign import ccall "prim_errno.h" eDOM :: Int
eDQUOT = Errno eDQUOT
  where foreign import ccall "prim_errno.h" eDQUOT :: Int
eEXIST = Errno eEXIST
  where foreign import ccall "prim_errno.h" eEXIST :: Int
eFAULT = Errno eFAULT
  where foreign import ccall "prim_errno.h" eFAULT :: Int
eFBIG = Errno eFBIG
  where foreign import ccall "prim_errno.h" eFBIG :: Int
eFTYPE = Errno eFTYPE
  where foreign import ccall "prim_errno.h" eFTYPE :: Int
eHOSTDOWN = Errno eHOSTDOWN
  where foreign import ccall "prim_errno.h" eHOSTDOWN :: Int
eHOSTUNREACH = Errno eHOSTUNREACH
  where foreign import ccall "prim_errno.h" eHOSTUNREACH :: Int
eIDRM = Errno eIDRM
  where foreign import ccall "prim_errno.h" eIDRM :: Int
eILSEQ = Errno eILSEQ
  where foreign import ccall "prim_errno.h" eILSEQ :: Int
eINPROGRESS = Errno eINPROGRESS
  where foreign import ccall "prim_errno.h" eINPROGRESS :: Int
eINTR = Errno eINTR
  where foreign import ccall "prim_errno.h" eINTR :: Int
eINVAL = Errno eINVAL
  where foreign import ccall "prim_errno.h" eINVAL :: Int
eIO = Errno eIO
  where foreign import ccall "prim_errno.h" eIO :: Int
eISCONN = Errno eISCONN
  where foreign import ccall "prim_errno.h" eISCONN :: Int
eISDIR = Errno eISDIR
  where foreign import ccall "prim_errno.h" eISDIR :: Int
eLOOP = Errno eLOOP
  where foreign import ccall "prim_errno.h" eLOOP :: Int
eMFILE = Errno eMFILE
  where foreign import ccall "prim_errno.h" eMFILE :: Int
eMLINK = Errno eMLINK
  where foreign import ccall "prim_errno.h" eMLINK :: Int
eMSGSIZE = Errno eMSGSIZE
  where foreign import ccall "prim_errno.h" eMSGSIZE :: Int
eMULTIHOP = Errno eMULTIHOP
  where foreign import ccall "prim_errno.h" eMULTIHOP :: Int
eNAMETOOLONG = Errno eNAMETOOLONG
  where foreign import ccall "prim_errno.h" eNAMETOOLONG :: Int
eNETDOWN = Errno eNETDOWN
  where foreign import ccall "prim_errno.h" eNETDOWN :: Int
eNETRESET = Errno eNETRESET
  where foreign import ccall "prim_errno.h" eNETRESET :: Int
eNETUNREACH = Errno eNETUNREACH
  where foreign import ccall "prim_errno.h" eNETUNREACH :: Int
eNFILE = Errno eNFILE
  where foreign import ccall "prim_errno.h" eNFILE :: Int
eNOBUFS = Errno eNOBUFS
  where foreign import ccall "prim_errno.h" eNOBUFS :: Int
eNODATA = Errno eNODATA
  where foreign import ccall "prim_errno.h" eNODATA :: Int
eNODEV = Errno eNODEV
  where foreign import ccall "prim_errno.h" eNODEV :: Int
eNOENT = Errno eNOENT
  where foreign import ccall "prim_errno.h" eNOENT :: Int
eNOEXEC = Errno eNOEXEC
  where foreign import ccall "prim_errno.h" eNOEXEC :: Int
eNOLCK = Errno eNOLCK
  where foreign import ccall "prim_errno.h" eNOLCK :: Int
eNOLINK = Errno eNOLINK
  where foreign import ccall "prim_errno.h" eNOLINK :: Int
eNOMEM = Errno eNOMEM
  where foreign import ccall "prim_errno.h" eNOMEM :: Int
eNOMSG = Errno eNOMSG
  where foreign import ccall "prim_errno.h" eNOMSG :: Int
eNONET = Errno eNONET
  where foreign import ccall "prim_errno.h" eNONET :: Int
eNOPROTOOPT = Errno eNOPROTOOPT
  where foreign import ccall "prim_errno.h" eNOPROTOOPT :: Int
eNOSPC = Errno eNOSPC
  where foreign import ccall "prim_errno.h" eNOSPC :: Int
eNOSR = Errno eNOSR
  where foreign import ccall "prim_errno.h" eNOSR :: Int
eNOSTR = Errno eNOSTR
  where foreign import ccall "prim_errno.h" eNOSTR :: Int
eNOSYS = Errno eNOSYS
  where foreign import ccall "prim_errno.h" eNOSYS :: Int
eNOTBLK = Errno eNOTBLK
  where foreign import ccall "prim_errno.h" eNOTBLK :: Int
eNOTCONN = Errno eNOTCONN
  where foreign import ccall "prim_errno.h" eNOTCONN :: Int
eNOTDIR = Errno eNOTDIR
  where foreign import ccall "prim_errno.h" eNOTDIR :: Int
eNOTEMPTY = Errno eNOTEMPTY
  where foreign import ccall "prim_errno.h" eNOTEMPTY :: Int
eNOTSOCK = Errno eNOTSOCK
  where foreign import ccall "prim_errno.h" eNOTSOCK :: Int
eNOTTY = Errno eNOTTY
  where foreign import ccall "prim_errno.h" eNOTTY :: Int
eNXIO = Errno eNXIO
  where foreign import ccall "prim_errno.h" eNXIO :: Int
eOPNOTSUPP = Errno eOPNOTSUPP
  where foreign import ccall "prim_errno.h" eOPNOTSUPP :: Int
ePERM = Errno ePERM
  where foreign import ccall "prim_errno.h" ePERM :: Int
ePFNOSUPPORT = Errno ePFNOSUPPORT
  where foreign import ccall "prim_errno.h" ePFNOSUPPORT :: Int
ePIPE = Errno ePIPE
  where foreign import ccall "prim_errno.h" ePIPE :: Int
ePROCLIM = Errno ePROCLIM
  where foreign import ccall "prim_errno.h" ePROCLIM :: Int
ePROCUNAVAIL = Errno ePROCUNAVAIL
  where foreign import ccall "prim_errno.h" ePROCUNAVAIL :: Int
ePROGMISMATCH = Errno ePROGMISMATCH
  where foreign import ccall "prim_errno.h" ePROGMISMATCH :: Int
ePROGUNAVAIL = Errno ePROGUNAVAIL
  where foreign import ccall "prim_errno.h" ePROGUNAVAIL :: Int
ePROTO = Errno ePROTO
  where foreign import ccall "prim_errno.h" ePROTO :: Int
ePROTONOSUPPORT = Errno ePROTONOSUPPORT
  where foreign import ccall "prim_errno.h" ePROTONOSUPPORT :: Int
ePROTOTYPE = Errno ePROTOTYPE
  where foreign import ccall "prim_errno.h" ePROTOTYPE :: Int
eRANGE = Errno eRANGE
  where foreign import ccall "prim_errno.h" eRANGE :: Int
eREMCHG = Errno eREMCHG
  where foreign import ccall "prim_errno.h" eREMCHG :: Int
eREMOTE = Errno eREMOTE
  where foreign import ccall "prim_errno.h" eREMOTE :: Int
eROFS = Errno eROFS
  where foreign import ccall "prim_errno.h" eROFS :: Int
eRPCMISMATCH = Errno eRPCMISMATCH
  where foreign import ccall "prim_errno.h" eRPCMISMATCH :: Int
eRREMOTE = Errno eRREMOTE
  where foreign import ccall "prim_errno.h" eRREMOTE :: Int
eSHUTDOWN = Errno eSHUTDOWN
  where foreign import ccall "prim_errno.h" eSHUTDOWN :: Int
eSOCKTNOSUPPORT = Errno eSOCKTNOSUPPORT
  where foreign import ccall "prim_errno.h" eSOCKTNOSUPPORT :: Int
eSPIPE = Errno eSPIPE
  where foreign import ccall "prim_errno.h" eSPIPE :: Int
eSRCH = Errno eSRCH
  where foreign import ccall "prim_errno.h" eSRCH :: Int
eSRMNT = Errno eSRMNT
  where foreign import ccall "prim_errno.h" eSRMNT :: Int
eSTALE = Errno eSTALE
  where foreign import ccall "prim_errno.h" eSTALE :: Int
eTIME = Errno eTIME
  where foreign import ccall "prim_errno.h" eTIME :: Int
eTIMEDOUT = Errno eTIMEDOUT
  where foreign import ccall "prim_errno.h" eTIMEDOUT :: Int
eTOOMANYREFS = Errno eTOOMANYREFS
  where foreign import ccall "prim_errno.h" eTOOMANYREFS :: Int
eTXTBSY = Errno eTXTBSY
  where foreign import ccall "prim_errno.h" eTXTBSY :: Int
eUSERS = Errno eUSERS
  where foreign import ccall "prim_errno.h" eUSERS :: Int
eWOULDBLOCK = Errno eWOULDBLOCK
  where foreign import ccall "prim_errno.h" eWOULDBLOCK :: Int
eXDEV = Errno eXDEV
  where foreign import ccall "prim_errno.h" eXDEV :: Int

isValidErrno :: Errno -> Bool
isValidErrno (Errno e) = e >= 0

foreign import ccall "errno.h &" errno :: Ptr CInt

getErrno :: IO Errno
getErrno = peekInt errno >>= \e -> return (Errno e)

resetErrno :: IO ()
resetErrno = pokeInt errno 0

errnoToIOError :: String -> Errno -> Maybe Handle -> Maybe String -> IOError
errnoToIOError loc (Errno e) _ _ = if null loc then cs else loc ++ ": " ++ cs
  where foreign import ccall "string.h" strerror :: CInt -> IO CString
        cs = unsafePerformIO (strerror e >>= peekCString)

throwErrno :: String -> IO a
throwErrno loc =
  getErrno >>= \e -> ioError (errnoToIOError loc e Nothing Nothing)

throwErrnoIf :: (a -> Bool) -> String -> IO a -> IO a
throwErrnoIf f loc m = m >>= \x -> if f x then throwErrno loc else return x

throwErrnoIf_ :: (a -> Bool) -> String -> IO a -> IO ()
throwErrnoIf_ f loc m = m >>= \x -> if f x then throwErrno loc else return ()

throwErrnoIfRetry :: (a -> Bool) -> String -> IO a -> IO a
throwErrnoIfRetry f loc m =
  m >>= \x ->
  if f x then
    getErrno >>= \e ->
    if e == eINTR then throwErrnoIfRetry f loc m else throwErrno loc
  else return x

throwErrnoIfRetry_ :: (a -> Bool) -> String -> IO a -> IO ()
throwErrnoIfRetry_ f loc m =
  m >>= \x ->
  if f x then
    getErrno >>= \e ->
    if e == eINTR then throwErrnoIfRetry_ f loc m else throwErrno loc
  else return ()

throwErrnoIfMinus1 :: String -> IO Int -> IO Int
throwErrnoIfMinus1 = throwErrnoIf (-1 ==)

throwErrnoIfMinus1_ :: String -> IO Int -> IO ()
throwErrnoIfMinus1_ = throwErrnoIf_ (-1 ==)

throwErrnoIfMinus1Retry :: String -> IO Int -> IO Int
throwErrnoIfMinus1Retry = throwErrnoIfRetry (-1 ==)

throwErrnoIfMinus1Retry_ :: String -> IO Int -> IO ()
throwErrnoIfMinus1Retry_ = throwErrnoIfRetry_ (-1 ==)

throwErrnoIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwErrnoIfNull = throwErrnoIf (nullPtr ==)

throwErrnoIfNullRetry :: String -> IO (Ptr a) -> IO (Ptr a)
throwErrnoIfNullRetry = throwErrnoIfRetry (nullPtr ==)
