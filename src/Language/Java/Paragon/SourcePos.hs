{-# LANGUAGE DeriveDataTypeable #-}
module Language.Java.Paragon.SourcePos where
-- | Simple module simulating SourcePos from ParSec that mainly
-- states that Eq should consider all instances of SourcePos
-- equal, to not mess up the existing code in Paragon.
import Data.Data (Data)
import Data.Typeable (Typeable)
import Text.ParserCombinators.Parsec.Pos as PS hiding (SourcePos)

-- | Paragon representation of source positions
data SourcePos = SourcePos String Int Int
  deriving (Data, Typeable)

-- | Create a new source code position representation
newPos :: String -> Int -> Int -> SourcePos
newPos = SourcePos

instance Eq SourcePos where
  _ == _ = True

-- Also provide instance for Ord, since Map.lookup uses that...
instance Ord SourcePos where
  _ <= _ = True

-- | Real equality operation
realEqSourcePos :: SourcePos -> SourcePos -> Bool
realEqSourcePos (SourcePos p1 l1 c1)
                (SourcePos p2 l2 c2) = p1 == p2 && l1 == l2 && c1 == c2

instance Show SourcePos where
  show (SourcePos p l c) = p ++ " (line " ++ show l ++ ", column " ++
                           show c ++ ")"

-- On purpose no type def, would have been:
-- extractPSPos :: SourcePos -> PS.SourcePos
-- but then we would have to qualify all SourcePos occurrences, bit messy
extractPSPos (SourcePos p l c) = PS.newPos p l c --undefined

-- Again on purpose no type def, would have been:
-- parSecToSourcePos :: PS.SourcePos -> SourcePos
parSecToSourcePos p = SourcePos (PS.sourceName   p)
                                (PS.sourceLine   p)
                                (PS.sourceColumn p)

-- | If the position of an error is not important or unknown, use this.
defaultPos :: SourcePos
defaultPos = SourcePos "" (-1) (-1)

-- | Return source position line and column
sourceLine, sourceColumn :: SourcePos -> Int
sourceLine   (SourcePos _ l _) = l
sourceColumn (SourcePos _ _ c) = c
