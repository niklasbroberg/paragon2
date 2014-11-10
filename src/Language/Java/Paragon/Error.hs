module Language.Java.Paragon.Error where

import Language.Java.Paragon.SourcePos

-- | Representing the context in which the error occurs
data ContextInfo
    = ClassContext            String 
    | MethodContext           String
    | LockStateContext        String
    | LockSignatureContext    String
    | ConstructorBodyContext  String
    | FallbackContext         String
    | EmptyContext
  deriving Show

-- | Representation of various error categories
-- organization plan: order by Object, Array, Assignment error etc.
data ErrorInfo
    = FallbackError     String
    | ParsingError      String
    
    | PolViolatedAss    String String String String
      
    -- The parser supports more features than the compiler (E.g. enums, 
    -- multi-class files.) Use this error type to indicate such errors
    | UnsupportedFeature String
    
    -- NameResolution 
    | UnresolvedName    String String
    | AmbiguousName     String String String String
    | IllegalDeref      String String 
      -- ^"."-operator called on the entity specified as 2nd param,
      -- of type specified by 1st param (e.g. lock/method)
    | EInPackage        String String String
      -- ^Expression as direct member of package
      -- Expression / Expression type (e.g. lock) / Package
    
    -- TcDeclM
    | FileClassMismatch String
    | FileInterfaceMismatch String
    | FileClassMismatchFetchType String String
    | VariableAlreadyDefined String
    | FieldAlreadyDefined String
    | PolicyAlreadyDefined String
    | ParameterAlreadyDefined String
    | MethodAlreadyDefined String
    | ConstructorAlreadyDefined

    -- TcCodeM
    | MissingReturnStatement
    | NonStaticMethodReferencedFromStatic String
    | NonStaticFieldReferencedFromStatic String

    -- TcExp
    | LArityMismatch    String Int Int
    | FieldLRTObject    String String String String
    | ArrayLRTIndex     String String String String
    | ExprLRTArray      String String String
    | NoSuchField       String String String
    | NonIntIndex       String
    | NonArrayIndexed   String String
    | NotSupported      String String  -- ^ description, value
    | NNFieldAssN       String String
    | TypeMismatch      String String
    | UnificationFailed String
    | WriteBounded      String String String String
     -- ^ lhs, policy lhs, write effect src, write effect bound
    | CondNotBool       String
    | BranchTypeMismatch
    | OpNotNumeric      String String -- ^ operator, type
    | OpNotIntegral     String String
    | OpNotBoolean      String String
    | WrongCastT
    | ArrayZeroDim
    | NonIntDimArray    String
    | ArrayDimPol       String String String
    | ArrayInitExpPol   String String String
    | MethodArgRestr    String String String String
  deriving Show
 

-- | An error consists of the actual error information, the position in the
-- file where the error originated and the context in which the error occurred.
data Error = Error {
  errorInfo :: ErrorInfo,
  errorPos :: SourcePos,
  errorContext :: [ContextInfo]
  }
  deriving Show

-- | Function for constructing an error, defaulting context to empty list.
mkError :: ErrorInfo -> SourcePos -> Error
mkError info pos = Error info pos []

-- | Construct error from error info alone (no additional context or position)
mkErrorFromInfo :: ErrorInfo -> Error
mkErrorFromInfo = flip mkError defaultPos

-- | Extend the current context such that this information can be added to any
-- potential error arising in this context.
addContextInfo :: ContextInfo -> Error -> Error
addContextInfo ci (Error info pos cont) = Error info pos (cont++[ci])

-- | Fallback function to convert old style error strings to the new
-- representation.
toUndef :: String -> Error
toUndef x = Error (FallbackError x) defaultPos []

--baseError :: String -> Error
--baseError s = ContextErrorC (BaseError s)

failEither :: Error -> Either Error a
failEither = Left

