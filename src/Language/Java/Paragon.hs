{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}
-- | Program entry point & coordination of compilation process
module Main where

-- Note: for the time being I converted most of this to explicit exports
-- to get a better overview what is where /jens
import Language.Java.Paragon.Syntax (CompilationUnit)
import Language.Java.Paragon.Parser (compilationUnit, parser, ParseError)
import Language.Java.Paragon.Pretty (prettyPrint)
import Language.Java.Paragon.NameResolution (resolveNames)
import Language.Java.Paragon.TypeCheck (T, typeCheck)
import Language.Java.Paragon.Compile (compileTransform)
import Language.Java.Paragon.PiGeneration (piTransform)
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos (parSecToSourcePos)
import Language.Java.Paragon.Error
import Language.Java.Paragon.ErrorTxt (errorTxt, errorTxtOld)
import Language.Java.Paragon.ErrorEclipse (errorEclipse)
import Language.Java.Paragon.Monad.Base

import System.FilePath
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs, getEnv)
import System.IO.Error (isDoesNotExistError)
import System.Exit
import Control.Exception (tryJust)
import Control.Monad
import Control.Monad.Trans.State ()
import Text.ParserCombinators.Parsec as PS (errorPos)
import Text.ParserCombinators.Parsec.Error (messageString, errorMessages)
import System.Console.GetOpt

-- | Main method, invokes the compiler
main :: IO ()
main = do
  (flags, files) <- compilerOpts =<< getArgs

  -- Parse verbosity flags and set using 'setVerbosity'.
  mapM_ setVerbosity [ k | Verbose k <- flags ]

  setCheckNull (NoNullCheck `notElem` flags)

  when (Version `elem` flags) -- When the flag Version is set
           $ normalPrint paracVersionString -- Print the version string (the
                                            -- function is defined in
                                            -- Interaction.hs
  -- When the flag help is set or no flags nor files were provided:
  when (Help    `elem` flags || null flags && null files)
           $ normalPrint $ usageInfo usageHeader options

  -- When files are specified, try to compile them
  unless (null files) $
    -- Case distinction only done to not break test suite:
    -- It expects explicit fail signaling
    if length files == 1 then
      do res <- compile flags (head files)
         hasErrors <- handleErrors flags [res]
         when hasErrors (exitWith $ ExitFailure (-1))
    else
      do res <- multiCompile flags files
         _ <- handleErrors flags res
         return ()

-- | All different flags that can be provided to the Paragon compiler
data Flag = Verbose Int | Version | Help | PiPath String | Eclipse | OldSkool | OutputPath String | SourcePath String | NoNullCheck
  deriving (Show, Eq)

-- | Two strings describing the version and the usage of the compiler
paracVersionString, usageHeader :: String
paracVersionString = "Paragon Compiler version: " ++ versionString
usageHeader = "Usage: parac [OPTION...] files..."

-- | List of available flags (-v -V -h -p)
options :: [OptDescr Flag]
options =
    -- Option and OptArg not defined, but assume they come from
    -- System.Console.GetOpt
    [ Option ['v'] ["verbose"]
                 (OptArg (Verbose . maybe 3 read) "n") -- default verbosity is 3
                 "Control verbosity (n is 0--4, normal verbosity level is 1, -v alone is equivalent to -v3)"
    , Option ['V'] ["version"]
                 (NoArg Version)       "Show version number"
    , Option ['h','?'] ["help"]
                 (NoArg Help)          "Show this help"
    , Option ['p'] ["pipath"]
                 (ReqArg PiPath "<path>") -- required argument
                 "Path to the root directory for Paragon interface (.pi) files (default is . )"
    , Option ['e'] ["eclipse"]
                 (NoArg Eclipse)       "Report output for eclipse (partly implemented)"
    , Option [] ["oldskool"]
                 (NoArg OldSkool)      "Report error messages in old school style"
    , Option ['o'] ["output"]
                 (ReqArg OutputPath "<path>")
                 "Output directory for generated .java and .pi files (default is same as source, i.e. -s should be provided)"
    , Option ['s'] ["source"]
                 (ReqArg SourcePath "<path>")
                 "Source directory for .para files (default is .)"
    , Option ['n'] ["nonull"]
                 (NoArg NoNullCheck)
                 "Do not check for flows via unchecked nullpointer exceptions"
    ]

-- |Converts the list of arguments to a pair of two lists of equal length.
-- The first lists the flags used, the second a list of files
-- that need to be compiled
compilerOpts :: [String]              -- ^ The list of arguments
             -> IO ([Flag], [String]) -- ^ Pair of flags + file names list
compilerOpts argv =
    -- RequireOrder --> no option processing after first non-option
    case getOpt RequireOrder options argv of
      (o,n,[]) -> return (o,n)
      -- in case of errors: show errors parsing arguments + usage info
      (_,_,errs) -> ioError (userError (concat errs ++ usageInfo usageHeader options))


-------------------------------------------------------------------------------------

-- | Handles the potential errors generated for each file.
-- Returns true iff there was at least one error
handleErrors :: [Flag] -> [(String, [Error])] -> IO Bool
handleErrors flags errors = do
  mapM_ (if OldSkool `elem` flags then errorTxtOld else
           if Eclipse `elem` flags then errorEclipse else errorTxt) errors -- TODO should be different function for XML ofc.
  return . not . null $ concatMap snd errors

-- | Collect paths to interface files from options and environment
buildPiPath :: [Flag] -> String -> IO [String]
buildPiPath flags filePath = do
  -- Using import System.FilePath, split path into directory and filename
  let (directoryRaw,_fileName) = splitFileName filePath
      -- Workaround for old and buggy 'filepath' versions
      -- Default is in this direcory
      _directory = if null directoryRaw then "./" else directoryRaw
  pp <- getPIPATH -- Read the PIPATH environment variable
  -- Concatenate two lists of directories where to look for pi files:
  -- ~ the explicitly defined ones with the -p flag
  -- ~ the ones coming from the environment variables
  -- If this set is empty, use the current directory.
  let pDirsSpec = concat [ splitSearchPath dir | PiPath dir <- flags ] ++ pp
      pDirs = if null pDirsSpec then ["./"] else pDirsSpec
  debugPrint $ show pDirs
  return pDirs

-- | Compile several files at once, return a list files and the errors
-- found in them (if any)
multiCompile :: [Flag] -> [String] -> IO [(String, [Error])]
multiCompile flags = mapM (
      \f -> do normalPrint $ "Compiling " ++ f
               compile flags f)

-- | Actual compiler function
compile :: [Flag]      -- ^ The flags specified as arguments to the compiler
        -> String      -- ^ Path to the .para file to compile (relative or absolute)
        -> IO (String, [Error])  -- ^ Name of compiled file and found errors
compile flags filePath = do
  -- Initialization: Set up environment and read file
  debugPrint $ "Filepath: " ++ filePath
  pDirs <- buildPiPath flags filePath
  fc <- readFile filePath

  -- Compilation
  res <- runBaseM . withDefaultErrCtxt $ compilationStages pDirs fc
  return (filePath, either id (const []) res) -- Return possibly empty list of errors

   where withDefaultErrCtxt = withErrCtxt EmptyContext
         compilationStages pDirs fc = do
           -- Converting to abstract syntax tree
           ast <- liftEitherMB . convertParseToErr $ parser compilationUnit fc
           raiseErrors
           detailPrint "Parsing complete!"
           -- Name resolution
           ast1 <- resolveNames pDirs ast
           raiseErrors
           detailPrint "Name resolution complete!"

           debugPrint $ prettyPrint ast1
           -- Type check
           ast2 <- typeCheck pDirs (takeBaseName filePath) ast1
           raiseErrors
           detailPrint "Type checking complete!"
           -- Generate .java and .pi files
           liftIO $ genFiles flags filePath  ast2
           detailPrint "File generation complete!"

convertParseToErr :: Either ParseError a -> Either Error a
convertParseToErr (Left x)  = Left $
   mkError (ParsingError $ messageString (head $ errorMessages x))
           (parSecToSourcePos $ PS.errorPos x)
convertParseToErr (Right x) = Right x

-- | Converts the environment variable PIPATH to a list of FilePaths
getPIPATH :: IO [FilePath]
getPIPATH = do
  -- guard indicates that the only expected exception is isDoesNotExistError
  -- returns an Either type, left exception, right path
  ePpStr <- tryJust (guard . isDoesNotExistError) $ getEnv "PIPATH"
  -- splitSearchPath comes from System.FilePath, splitting String into filepaths
  -- In case the PIPATH variable did not exist, the empty list is used.
  -- (either takes two functions, const makes a function ignoring the other
  -- argument, i.e. the exception is ignored).
  return $ splitSearchPath $ either (const []) id ePpStr

-- | Generate .pi and .java files
genFiles :: [Flag] -> FilePath -> CompilationUnit T -> IO ()
genFiles flags filePath ast  = let -- create .java ast
                             astC      = compileTransform ast
                             -- create .pi ast
                             astPi     = piTransform (void ast)
                             -- output to right files
                             baseName  = takeBaseName filePath
                             directory = takeDirectory filePath
                             outdir    = getOutdir flags </> makeRelative (getIndir flags) directory
                             javaPath  = outdir </> baseName <.> "java"
                             piPath    = outdir </> baseName <.> "pi"
                             java,pifile :: String
                             java      = prettyPrint astC
                             pifile    = prettyPrint astPi
                         in do createDirectoryIfMissing True outdir
                               writeFile javaPath java
                               >> writeFile piPath pifile
  where getOutdir []               = "."
        getOutdir (OutputPath p:_) = p
        getOutdir (_:xs)           = getOutdir xs
        getIndir []               = "."
        getIndir (SourcePath p:_) = p
        getIndir (_:xs)           = getIndir xs
