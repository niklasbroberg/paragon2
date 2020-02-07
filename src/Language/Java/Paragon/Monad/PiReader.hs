{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Language.Java.Paragon.Monad.PiReader
    (
      module Language.Java.Paragon.Monad.Base,

      PiPath, PiReader, runPiReader,

      MonadPR(..),

      getPiPath,
      doesPkgExist, doesTypeExist,
      getPkgContents, getTypeContents,
      getPiPathContents

    ) where

import Language.Java.Paragon.Syntax (Name(..), NameType(..), CompilationUnit, Ident(..))
import Language.Java.Paragon.Pretty (prettyPrint)
import Language.Java.Paragon.Parser (parser, compilationUnit)
import Language.Java.Paragon.SourcePos (SourcePos)
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.Monad.Base

import System.FilePath ((</>),(<.>),splitExtension)
import System.Directory (doesFileExist, doesDirectoryExist, getDirectoryContents)

import qualified Data.ByteString.Char8 as B
import Data.Char (toLower)

import Control.Monad (liftM, filterM, ap)
import Control.Arrow (second)
import qualified Control.Monad.Fail as Fail

piReaderModule :: String
piReaderModule = libraryBase ++ ".Monad.PiReader"

type PiPath = [FilePath] -- Should be a choice of many different

-- |Monad that adds an PiPath environment to the base monad
newtype PiReader a = PiReader ( PiPath -> BaseM a )

-- |Transform a PiReader into a BaseM computation by providing a pi-path env
-- This does not actually run the monadic computation, so maybe somewhat
-- misleading name?
runPiReader :: PiPath -> PiReader a -> BaseM a
runPiReader pp (PiReader f) = f pp

instance Applicative PiReader where
  (<*>) = ap
  pure = return

instance Fail.MonadFail PiReader where
  fail = liftBase . fail

instance Monad PiReader where
  return x = PiReader $ \_ -> return x

  PiReader f >>= k = PiReader $ \pp -> do
                          a <- f pp
                          let PiReader g = k a
                           in g pp
  fail = Fail.fail


instance Functor PiReader where
  fmap = liftM

instance MonadBase PiReader where
  liftBase ba = PiReader $ const ba
  withErrCtxt' ecf (PiReader f) = PiReader $ withErrCtxt' ecf . f
  tryM (PiReader f) = PiReader $ tryM . f
  failE = liftBase . failE
  failEC x = liftBase . failEC x

instance MonadIO PiReader where
  liftIO = liftBase . liftIO

class MonadBase m => MonadPR m where
  liftPR :: PiReader a -> m a
--  liftPRWith :: (PiReader a -> PiReader a) -> m a -> m a

instance MonadPR PiReader where
  liftPR = id
--  liftPRWith = id

-- |Read pi path from environment
getPiPathPR :: PiReader PiPath
getPiPathPR = PiReader return

-- |Read pi path from environment
getPiPath :: MonadPR m => m PiPath
getPiPath = liftPR getPiPathPR

---------------------------------------------------
-- The real functionality: reading pi files

-- |Checks if there is a directory corresponding to the given package name
-- in the pi-path environment
doesPkgExist :: MonadPR m => Name a -> m Bool
doesPkgExist pkgName = liftPR $ do
  let path = pNameToDir pkgName
  piPath <- getPiPath
  or <$> mapM (\p -> liftIO $ doesDirectoryExist $ p </> path) piPath

-- |Checks if there is a file corresponding to the given type name
-- in the pi-path environment
doesTypeExist :: MonadPR m => Name a -> m Bool
doesTypeExist typeName = liftPR $ do
  let path = tNameToFile typeName
  piPath <- getPiPath
  liftIO $ go piPath path

  where go [] _ = return False
        go (p:pis) path = do
              let fp = p </> path
              debugPrint $ "Checking for " ++ fp
              found <- doesFileExist fp
              if found
               then do
                 debugPrint $ "Found " ++ fp
                 return True
               else go pis path

-- |Returns the list of all .pi files in the package
-- Note: If more than 1 corresponding directory in path, the first is selected
getPkgContents :: MonadPR m => Name a -> m [B.ByteString]
getPkgContents pkgName = liftPR $ do
  let path = pNameToDir pkgName
  piPath <- getPiPath
  completePath <- selectFirstPkg path piPath
  readContents completePath

      where selectFirstPkg :: FilePath -> [FilePath] -> PiReader FilePath
            selectFirstPkg _ [] = panic (piReaderModule ++ ".getPkgContents")
                                ("No such package exists - doesPkgExist not called successfully"
                                 ++ show pkgName)
            selectFirstPkg path (pip:pips) = do
                     isP <- liftIO $ doesDirectoryExist $ pip </> path
                     if isP then return $ pip </> path
                            else selectFirstPkg path pips

            readContents :: FilePath -> PiReader [B.ByteString]
            readContents path = do
              files <- liftIO $ getDirectoryContents path
              return $ filterPiIdents files

-- |Returns all the packages and types found at the top level of the pi-path
-- The result is of the form (list of types, list of packages)
getPiPathContents :: MonadPR m => m ([B.ByteString], [B.ByteString])
getPiPathContents = do
  pp <- getPiPath
  liftIO $ go pp ([],[])

      where go :: [FilePath] -> ([B.ByteString], [B.ByteString])
               -> IO ([B.ByteString], [B.ByteString])
            go [] acc = return acc
            go (p:pis) (ts,ps) = do
                       isDir <- doesDirectoryExist p
                       if isDir then do
                                  files <- getDirectoryContents p
                                  pkgs  <- filterPkgIdentsM p files
                                  let tys = filterPiIdents files
                                  go pis (tys++ts,pkgs++ps)
                        else go pis (ts,ps)

-- |Find and parse .pi file for given AST name
-- Note: If more than 1 corresponding file in path, the first is selected
getTypeContents :: MonadPR m => Name a -> m (CompilationUnit SourcePos)
getTypeContents n = liftPR $ do
  let path = tNameToFile n
  piPath <- getPiPath
  findFirstPi path piPath

      where findFirstPi :: FilePath -> [FilePath] -> PiReader (CompilationUnit SourcePos)
            findFirstPi _ [] = panic (piReaderModule ++ ".getTypeContents")
                               ("No such type exists - doesTypeExist not called successfully: "
                                ++ show n)
            findFirstPi path (pip:pips) = do
                      isT <- liftIO $ doesFileExist $ pip </> path
                      if isT
                       then do fc <- liftIO $ readFile $ pip </> path
                               let pRes = parser compilationUnit fc
                               case pRes of
                                 Right cu -> return cu
                                 Left pe  -> fail $ "Parse error in pi file for type "
                                                   ++ prettyPrint n ++ ":\n"
                                                   ++ show pe
                       else findFirstPi path pips



---- Helper functions

-- |Return only the names of files with .pi extension. The extension is dropped
filterPiIdents :: [FilePath] -> [B.ByteString]
filterPiIdents files =
    let fnses = map (second stringToLower . splitExtension) files
    in [ B.pack str | (str, ".pi") <- fnses, not (null str), head str /= '.' ]
  where stringToLower = map toLower

-- |Given a directory and a list of directory names relative to that directory,
-- returns the list of directories that actually exist
-- and do not start with . (hidden)
filterPkgIdentsM :: MonadIO m => FilePath -> [FilePath] -> m [B.ByteString]
filterPkgIdentsM dir files = liftIO $ do
    fs <- filterM (doesDirectoryExist . (dir </>)) files
    return [ B.pack f | f <- fs, head f /= '.' ]

-- |Convert AST package name representation to file path to package directory
pNameToDir :: Name a -> FilePath
pNameToDir (Name _ PName mPre (Ident _ str)) =
    let pf = case mPre of
               Nothing -> id
               Just pre -> let fp = pNameToDir pre in (fp </>)
    in pf (B.unpack str)
pNameToDir (Name _ TName _ _) = fail "Inner types not supported"
pNameToDir n = panic (piReaderModule ++ ".pNameToDir") $ show n

-- |Convert AST type name representation to file path to actual .pi file
tNameToFile :: Name a -> FilePath
tNameToFile (Name _ TName mPre (Ident _ str)) =
    let pf = case mPre of
               Nothing -> id
               Just pre -> let fp = pNameToDir pre in (fp </>)
    in pf (B.unpack str) <.> "pi"
tNameToFile n = panic (piReaderModule ++ ".tNameToFile") $ show n
