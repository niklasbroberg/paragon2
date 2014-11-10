-- | Defines various function in the context of user interaction,
-- most importantly the verbosity settings and logging mechanism
module Language.Java.Paragon.Interaction
    (setVerbosity, getVerbosity, verbosePrint,
     --enableXmlOutput, getXmlOutput, -- Not used right now
     setCheckNull, checkNull,
     normalPrint, detailPrint, finePrint, debugPrint, tracePrint,
     panic,
     formatData,
     versionString, libraryBase, typeCheckerBase
    ) where

import Data.IORef
import Control.Monad
import System.IO.Unsafe (unsafePerformIO) -- Trust me, I know what I'm doing... :-D

-- Comment out to get rid of dependency on haskell-src-exts:
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Pretty

import Language.Java.Paragon.Monad.Base

-------------------------------------------------------------
-- Verbosity in feedback

{-# NOINLINE unsafeVerbosityGlobalVar #-}
unsafeVerbosityGlobalVar :: IORef Int
-- ^Stores the verbosity level as an Int in an IO Reference. 
-- Set to 1 by default.
unsafeVerbosityGlobalVar = unsafePerformIO $ newIORef 1

-- | Read verbosity level from IO reference
getVerbosity :: IO Int
getVerbosity = readIORef unsafeVerbosityGlobalVar

-- | Set the verbosity as an IO reference, i.e. 'unsafeVerbosityGlobalVar'
setVerbosity :: Int -> IO ()
setVerbosity k = writeIORef unsafeVerbosityGlobalVar k

-- | Conditional print function, comparing given and global verbosity levels
verbosePrint :: MonadIO m => Int -> String -> m ()
verbosePrint n str = liftIO $ do
  k <- getVerbosity
  when (n <= k) $ putStrLn str

-- | Mapping print functions to call to the 'verbosePrint' function with
-- increasing verbosity
normalPrint, detailPrint, finePrint, debugPrint, tracePrint :: MonadIO m => String -> m ()
normalPrint = verbosePrint 1      -- ^Feedback to the user in the normal case
detailPrint = verbosePrint 2      -- ^Report individual members
finePrint   = verbosePrint 3      -- ^Report verbosely (default for -v)
debugPrint  = verbosePrint 4      -- ^Include DEBUG output
tracePrint  = verbosePrint 5      -- ^State and env changes

-- This trace function uses haskell-src-exts to get nice formating.
-- To avoid depending on this package, comment out this version and the imports above, and
-- comment in the version using show below. 
formatData :: Show a => a -> String
formatData s = case parseExp (show s) of
    ParseOk x -> prettyPrintStyleMode 
      -- ribbonsPerLine adjust how eager the printer is to break lines eg in records.
      Style{ mode = PageMode, lineLength = 150, ribbonsPerLine = 2.5 } defaultMode x
    ParseFailed{} -> show s
-- formatData = show

unsafeCheckNullGlobalVar :: IORef Bool
unsafeCheckNullGlobalVar = unsafePerformIO $ newIORef False
checkNull :: IO Bool
checkNull = readIORef unsafeCheckNullGlobalVar
setCheckNull :: Bool -> IO ()
setCheckNull b = writeIORef unsafeCheckNullGlobalVar b

-------------------------------------------------------------
-- Generate XML output
-- [Currently unused]

{-
{-# NOINLINE unsafeXmlOutputGlobalVar #-}

unsafeXmlOutputGlobalVar :: IORef Bool
unsafeXmlOutputGlobalVar = unsafePerformIO $ newIORef False

getXmlOutput :: IO Bool
getXmlOutput = readIORef unsafeXmlOutputGlobalVar

enableXmlOutput :: IO ()
enableXmlOutput = writeIORef unsafeXmlOutputGlobalVar True
-}
--xmlOutput :: IORef XMLNode
--xmlOutput = unsafePerformIO $ newIORef $ 
--            XMLNode "parac" [XMLAttribute "version" versionString] []

--insertXMLNode :: XMLNode -> IO ()
--insertXMLNode n = readIORef (xmlOutput) >>= \x -> writeIORef xmlOutput (insertNode x n)


-------------------------------------------------------------

-- | A function for generating bug report guidelines
panic :: String -> String -> a
panic cause extra = error $ "Panic! " ++ cause ++ " caused the impossible, \
                            \and the world is now about to end in 3.. 2.. 1.. \n\
                            \Please report as a bug at: " ++ issueTracker ++
                            if not (null extra) 
                            then "\nExtra information: " ++ extra
                            else ""

issueTracker :: String
issueTracker = "http://code.google.com/p/paragon-java/issues/entry"

versionString :: String
versionString = "0.1.31"

-- | Module paths for use in error reports
libraryBase, typeCheckerBase :: String
libraryBase = "Language.Java.Paragon"
typeCheckerBase = libraryBase ++ ".TypeCheck"
