-- $Id: ForeignPtr.curry 2125 2007-03-18 21:31:02Z wlux $
--
-- Copyright (c) 2005-2007, Wolfgang Lux
-- See ../LICENSE for the full license.

module ForeignPtr where
import Ptr
import MarshalAlloc

type FinalizerPtr a        = FunPtr (           Ptr a -> IO ())
type FinalizerEnvPtr env a = FunPtr (Ptr env -> Ptr a -> IO ())

data ForeignPtr a

foreign import rawcall "foreign.h primNewForeignPtr"
        newForeignPtr_ :: Ptr a -> IO (ForeignPtr a)

newForeignPtr :: FinalizerPtr a -> Ptr a -> IO (ForeignPtr a)
newForeignPtr finalizer ptr =
  do
    fp <- newForeignPtr_ ptr
    addForeignPtrFinalizer finalizer fp
    return fp

newForeignPtrEnv :: FinalizerEnvPtr env a -> Ptr env -> Ptr a
                 -> IO (ForeignPtr a)
newForeignPtrEnv finalizer env ptr =
  do
    fp <- newForeignPtr_ ptr
    addForeignPtrFinalizerEnv finalizer env fp
    return fp

foreign import rawcall "foreign.h primAddForeignPtrFinalizer"
        addForeignPtrFinalizer :: FinalizerPtr a -> ForeignPtr a -> IO ()
foreign import rawcall "foreign.h primAddForeignPtrFinalizerEnv"
        addForeignPtrFinalizerEnv :: FinalizerEnvPtr env a -> Ptr env
                                  -> ForeignPtr a -> IO ()

mallocForeignPtrBytes :: Int -> IO (ForeignPtr a)
mallocForeignPtrBytes n = mallocBytes n >>= newForeignPtr finalizerFree

withForeignPtr :: ForeignPtr a -> (Ptr a -> IO b) -> IO b
withForeignPtr fp f =
  do
    x <- f (unsafeForeignPtrToPtr fp)
    touchForeignPtr fp
    return x

foreign import rawcall "foreign.h primUnsafeForeignPtrToPtr"
	       unsafeForeignPtrToPtr :: ForeignPtr a -> Ptr a
foreign import rawcall "foreign.h primTouchForeignPtr"
	       touchForeignPtr :: ForeignPtr a -> IO ()
foreign import rawcall "prims.h primCastPtr"
	       castForeignPtr :: ForeignPtr a -> ForeignPtr b
