-- | Transform an error to a user-friendly string.
module Language.Java.Paragon.ErrorEclipse (errorEclipse) where

import Language.Java.Paragon.Error
import Language.Java.Paragon.SourcePos

-- | Prints error information for all errors found in this file
errorEclipse :: (String, [Error]) -> IO ()
errorEclipse (_, []) = return ()
errorEclipse (_, err) =
  mapM_ (\(Error info pos _context) -> do
    putStr   $ dispSourcePos pos
    putStrLn $ errorTxt' info
    ) (reverse err)


-- | Displays name of the file, line in the file and an ascii-art arrow
-- pointing to the column in the specified sourcepos (unless the position is
-- the default, in which case only the name of the file is shown).
dispSourcePos :: SourcePos -> String
dispSourcePos pos =
  if realEqSourcePos pos defaultPos
    then "1:1:1:"
    else show (sourceLine pos)       ++ ":" ++
         show (sourceColumn pos - 1) ++ ":" ++
         show (sourceColumn pos - 1) ++ ":"

-- | Convert an error to a human readable string
errorTxt' :: ErrorInfo -> String
-- NameResolution
errorTxt' (UnresolvedName typ name) =
  "Unresolved name: " ++ typ ++ " " ++ name ++ " not in scope"

errorTxt' (AmbiguousName nt ident pre1 pre2) =
  "Ambiguous " ++ nt ++ " " ++ ident ++
    "\\nCould refer to either of:" ++
    "\\n    " ++ pre1 ++
    "\\n    " ++ pre2

errorTxt' (IllegalDeref typ name) =
  "Cannot dereference " ++ typ ++ ": " ++ name

errorTxt' (EInPackage expr expType pkg) =
  "Package " ++ pkg ++ " cannot have " ++ expType ++ " " ++ expr ++
                   " as a direct member."

-- TcDeclM
errorTxt' (FileClassMismatchFetchType fname cname) =
  "Filename " ++ fname ++ " does not match expected class name " ++ cname

-- TcExp
errorTxt' (LArityMismatch lname expr got) =
  "Lock " ++ lname ++ " expects " ++ show expr ++ " arguments, but has been "
  ++ "given " ++ show got ++ "."

errorTxt' (FieldLRTObject field obj opol fpol) =
  "Cannot update field " ++ field ++ " of object " ++ obj ++
  ": policy of field must be no less restrictive than that of the " ++
  "object when updating.\\n" ++
  "Object policy: " ++ opol ++ "\\n" ++
  "Field policy: " ++ fpol

errorTxt' (ArrayLRTIndex arr arrP ind indP) =
  "When assigning into an array, the policy on the index expression may be no "
  ++ "more restrictive than the policy of the array itself\\n" ++
  "Array: " ++ arr ++ "\\n" ++
  "  has policy " ++ arrP ++ "\\n" ++
  "Index: " ++ ind ++ "\\n" ++
  "  has policy " ++ indP

errorTxt' (ExprLRTArray expr arrP expP) =
  "Cannot update element in array resulting from expression " ++ expr ++
 ": policy of elements must be no less restrictive than that of the " ++
 "array itself when updating\\n" ++
 "Array policy: " ++ arrP ++ "\\n" ++
 "Element policy: " ++ expP

errorTxt' (NoSuchField oref otype field) =
  "Object " ++ oref ++ " of type " ++ otype ++ " does not have a field named "
  ++ field

errorTxt' (PolViolatedAss frEx frPo toEx toPo) =
  "Cannot assign result of expression " ++ frEx ++ " with policy " ++ frPo ++
  " to location " ++ toEx ++ " with policy " ++ toPo

errorTxt' (NonIntIndex ty) =
  "Non-integral expression of type " ++ ty ++ " used as array index expression"

errorTxt' (NonArrayIndexed expr ty) =
  "Cannot index non-array expression " ++ expr ++ " of type " ++ ty

errorTxt' (NotSupported sort val) =
  "Not supported " ++ sort ++ ": " ++ val

errorTxt' (NNFieldAssN field expr) =
  "Field " ++ field ++ " can't be assigned to the potentially null expression "
  ++ expr

errorTxt' (TypeMismatch ty1 ty2) =
  "Type mismatch: " ++ ty1 ++ " <=> " ++ ty2

errorTxt' (UnificationFailed loc)=
  "Cannot unify policy type parameters at " ++ loc

errorTxt' (WriteBounded lhs lhsP src writeB) =
  "Assignment to " ++ lhs ++ " with policy " ++ lhsP ++
  " not allowed in " ++ src ++ " with write effect bound " ++ writeB

errorTxt' (CondNotBool ty) =
  "Conditional expression requires a condition of type compatible with boolean"
  ++ "\\nFound type: " ++ ty

errorTxt' BranchTypeMismatch =
  "Types of branches don't match"

errorTxt' (OpNotIntegral op ty) =
  op ++ " operator used at non-integral type " ++ ty

errorTxt' (OpNotBoolean op ty) =
  op ++ " operator used at non-boolean type " ++ ty

errorTxt' (OpNotNumeric op ty) =
  op ++ " operator used at non-numeric type " ++ ty

errorTxt' WrongCastT =
  "Wrong type at cast"

errorTxt' ArrayZeroDim =
  "Array creation must have at least one dimension expression, or an explicit "
  ++ "initializer"

errorTxt' (NonIntDimArray ty) =
  "Non-integral expression of type " ++ ty ++
  " used as dimension expression in array creation"

errorTxt' (ArrayDimPol expr pol polB) =
  "Array dimension expression has too restrictive policy:\\n" ++
  "Expression: " ++ expr ++ "\\n" ++
  "  with policy: " ++ pol ++ "\\n" ++
  "Declared policy bound: " ++ polB

errorTxt' (ArrayInitExpPol expr exprP polB) =
  "Expression in array initializer has too restrictive policy:\\n" ++
  "Expression: " ++ expr ++ "\\n" ++
  "  with policy: " ++ exprP ++ "\\n" ++
  "Declared policy bound: " ++ polB


errorTxt' (ParsingError p) =
  "Parsing error: " ++ p

errorTxt' (FallbackError e) = e

-- Others
errorTxt' e =
  "Extra error: Show instance for this error not available:\\n" ++ show e
