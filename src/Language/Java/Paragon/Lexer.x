{
{-# OPTIONS_GHC
    -fno-warn-unused-matches
    -fno-warn-name-shadowing
    -fno-warn-missing-signatures
    -fno-warn-unused-binds
 #-}
module Language.Java.Paragon.Lexer (L(..), Token(..), lexer) where

import Numeric
import Data.Char (toLower, isHexDigit, isOctDigit)

}

%wrapper "posn"

$digit      = [0-9]
$nonzero    = [1-9]
$octdig     = [0-7]
$hexdig     = [0-9A-Fa-f]

@lineterm = [\n\r] | \r\n

-- TODO: this doesn't notice a comment that ends "**/"
@tradcomm = "/*" ( ~[\*] | \*+ (~[\/\*] | \n) | \n )* \*+ "/"
@linecomm = "//" .* @lineterm
@comm = @tradcomm | @linecomm

$javaLetter = [a-zA-Z\_\$]
$javaDigit = $digit
$javaLetterOrDigit = [a-zA-Z0-9\_\$]

@octEscape = [0123]? $octdig{1,2}
@hexEscape = u $hexdig{4}
@charEscape = \\ (@octEscape | @hexEscape | [btnfr\"\'\\])

@expsuffix = [\+\-]? $digit+
@exponent = [eE] @expsuffix
@pexponent = [pP] @expsuffix

tokens  :-

    $white+         ;
    @comm           ;

    abstract        { \p _ -> L (posn p) $ KW_Abstract     }
    assert          { \p _ -> L (posn p) $ KW_Assert       }
    boolean         { \p _ -> L (posn p) $ KW_Boolean      }
    break           { \p _ -> L (posn p) $ KW_Break        }
    byte            { \p _ -> L (posn p) $ KW_Byte         }
    case            { \p _ -> L (posn p) $ KW_Case         }
    catch           { \p _ -> L (posn p) $ KW_Catch        }
    char            { \p _ -> L (posn p) $ KW_Char         }
    class           { \p _ -> L (posn p) $ KW_Class        }
    const           { \p _ -> L (posn p) $ KW_Const        }
    continue        { \p _ -> L (posn p) $ KW_Continue     }
    default         { \p _ -> L (posn p) $ KW_Default      }
    do              { \p _ -> L (posn p) $ KW_Do           }
    double          { \p _ -> L (posn p) $ KW_Double       }
    else            { \p _ -> L (posn p) $ KW_Else         }
    enum            { \p _ -> L (posn p) $ KW_Enum         }
    extends         { \p _ -> L (posn p) $ KW_Extends      }
    final           { \p _ -> L (posn p) $ KW_Final        }
    finally         { \p _ -> L (posn p) $ KW_Finally      }
    float           { \p _ -> L (posn p) $ KW_Float        }
    for             { \p _ -> L (posn p) $ KW_For          }
    goto            { \p _ -> L (posn p) $ KW_Goto         }
    if              { \p _ -> L (posn p) $ KW_If           }
    implements      { \p _ -> L (posn p) $ KW_Implements   }
    import          { \p _ -> L (posn p) $ KW_Import       }
    instanceof      { \p _ -> L (posn p) $ KW_Instanceof   }
    int             { \p _ -> L (posn p) $ KW_Int          }
    interface       { \p _ -> L (posn p) $ KW_Interface    }
    long            { \p _ -> L (posn p) $ KW_Long         }
    native          { \p _ -> L (posn p) $ KW_Native       }
    new             { \p _ -> L (posn p) $ KW_New          }
    package         { \p _ -> L (posn p) $ KW_Package      }
    private         { \p _ -> L (posn p) $ KW_Private      }
    protected       { \p _ -> L (posn p) $ KW_Protected    }
    public          { \p _ -> L (posn p) $ KW_Public       }
    return          { \p _ -> L (posn p) $ KW_Return       }
    short           { \p _ -> L (posn p) $ KW_Short        }
    static          { \p _ -> L (posn p) $ KW_Static       }
    strictfp        { \p _ -> L (posn p) $ KW_Strictfp     }
    super           { \p _ -> L (posn p) $ KW_Super        }
    switch          { \p _ -> L (posn p) $ KW_Switch       }
    synchronized    { \p _ -> L (posn p) $ KW_Synchronized }
    this            { \p _ -> L (posn p) $ KW_This         }
    throw           { \p _ -> L (posn p) $ KW_Throw        }
    throws          { \p _ -> L (posn p) $ KW_Throws       }
    transient       { \p _ -> L (posn p) $ KW_Transient    }
    try             { \p _ -> L (posn p) $ KW_Try          }
    void            { \p _ -> L (posn p) $ KW_Void         }
    volatile        { \p _ -> L (posn p) $ KW_Volatile     }
    while           { \p _ -> L (posn p) $ KW_While        }

    actor           { \p _ -> L (posn p) $ KW_P_Actor      }
    close           { \p _ -> L (posn p) $ KW_P_Close      }
    lock            { \p _ -> L (posn p) $ KW_P_Lock       }
--    newactor        { \p _ -> L (posn p) $ KW_P_Newactor   }
    notnull         { \p _ -> L (posn p) $ KW_P_Notnull    }
    open            { \p _ -> L (posn p) $ KW_P_Open       }
    policy          { \p _ -> L (posn p) $ KW_P_Policy     }
    when            { \p _ -> L (posn p) $ KW_P_When       }
    typemethod 	    { \p _ -> L (posn p) $ KW_P_Typemethod }
    policyof        { \p _ -> L (posn p) $ KW_P_Policyof   }
    readonly        { \p _ -> L (posn p) $ KW_P_Readonly   }
    reflexive	    { \p _ -> L (posn p) $ KW_P_Reflexive  }
    transitive	    { \p _ -> L (posn p) $ KW_P_Transitive }
    symmetric	    { \p _ -> L (posn p) $ KW_P_Symmetric  }

    0               { \p _ -> L (posn p) $ IntTok 0        }
    0 [lL]          { \p _ -> L (posn p) $ LongTok 0       }
    0 $digit+       { \p s -> L (posn p) $ IntTok (pickyReadOct s) }
    0 $digit+ [lL]  { \p s -> L (posn p) $ LongTok (pickyReadOct (init s)) }
    $nonzero $digit*        { \p s -> L (posn p) $ IntTok (read s) }
    $nonzero $digit* [lL]   { \p s -> L (posn p) $ LongTok (read (init s)) }
    0 [xX] $hexdig+         { \p s -> L (posn p) $ IntTok (fst . head $ readHex (drop 2 s)) }
    0 [xX] $hexdig+ [lL]    { \p s -> L (posn p) $ LongTok (fst . head $ readHex (init (drop 2 s))) }

    $digit+ \. $digit* @exponent? [dD]?           { \p s -> L (posn p) $ DoubleTok (fst . head $ readFloat $ '0':s) }
            \. $digit+ @exponent? [dD]?           { \p s -> L (posn p) $ DoubleTok (fst . head $ readFloat $ '0':s) }
    $digit+ \. $digit* @exponent? [fF]            { \p s -> L (posn p) $ FloatTok  (fst . head $ readFloat $ '0':s) }
            \. $digit+ @exponent? [fF]            { \p s -> L (posn p) $ FloatTok  (fst . head $ readFloat $ '0':s) }
    $digit+ @exponent                             { \p s -> L (posn p) $ DoubleTok (fst . head $ readFloat s) }
    $digit+ @exponent? [dD]                       { \p s -> L (posn p) $ DoubleTok (fst . head $ readFloat s) }
    $digit+ @exponent? [fF]                       { \p s -> L (posn p) $ FloatTok  (fst . head $ readFloat s) }
    0 [xX] $hexdig* \.? $hexdig* @pexponent [dD]? { \p s -> L (posn p) $ DoubleTok (readHexExp (drop 2 s)) }
    0 [xX] $hexdig* \.? $hexdig* @pexponent [fF]  { \p s -> L (posn p) $ FloatTok  (readHexExp (drop 2 s)) }

    true            { \p _ -> L (posn p) $ BoolTok True    }
    false           { \p _ -> L (posn p) $ BoolTok False   }

-- HERE
--    ' $javaLetter $javaLetterOrDigit*   { \p s -> L (posn p) $ VarActorTok (tail s) }

    ' (@charEscape | ~[\\\']) '               { \p s -> L (posn p) $ CharTok (readCharTok s) }

    \" (@charEscape | ~[\\\"])* \"            { \p s -> L (posn p) $ StringTok (readStringTok s) }

    null            {\p _ -> L (posn p) $ NullTok }

    \#N\# $javaLetter $javaLetterOrDigit*     { \p s -> L (posn p) $ AntiQNameTok  (drop 3 s) }
    \#E\# $javaLetter $javaLetterOrDigit*     { \p s -> L (posn p) $ AntiQExpTok   (drop 3 s) }
    \#T\# $javaLetter $javaLetterOrDigit*     { \p s -> L (posn p) $ AntiQTypeTok  (drop 3 s) }
    \#    $javaLetter $javaLetterOrDigit*     { \p s -> L (posn p) $ AntiQIdentTok (drop 1 s) }

    $javaLetter $javaLetterOrDigit*     { \p s -> L (posn p) $ IdentTok s }

    \(              { \p _ -> L (posn p) $ OpenParen       }
    \)              { \p _ -> L (posn p) $ CloseParen      }
    \[              { \p _ -> L (posn p) $ OpenSquare      }
    \]              { \p _ -> L (posn p) $ CloseSquare     }
    \{              { \p _ -> L (posn p) $ OpenCurly       }
    \}              { \p _ -> L (posn p) $ CloseCurly      }
    \;              { \p _ -> L (posn p) $ SemiColon       }
    \,              { \p _ -> L (posn p) $ Comma           }
    \.              { \p _ -> L (posn p) $ Period          }

    "="             { \p _ -> L (posn p) $ Op_Equal        }
    ">"             { \p _ -> L (posn p) $ Op_GThan        }
    "<"             { \p _ -> L (posn p) $ Op_LThan        }
    "!"             { \p _ -> L (posn p) $ Op_Bang         }
    "~"             { \p _ -> L (posn p) $ Op_Tilde        }
    "?"             { \p _ -> L (posn p) $ Op_Query        }
    ":"             { \p _ -> L (posn p) $ Op_Colon        }
    "=="            { \p _ -> L (posn p) $ Op_Equals       }
    "<="            { \p _ -> L (posn p) $ Op_LThanE       }
    ">="            { \p _ -> L (posn p) $ Op_GThanE       }
    "!="            { \p _ -> L (posn p) $ Op_BangE        }
    "&&"            { \p _ -> L (posn p) $ Op_AAnd         }
    "||"            { \p _ -> L (posn p) $ Op_OOr          }
    "++"            { \p _ -> L (posn p) $ Op_PPlus        }
    "--"            { \p _ -> L (posn p) $ Op_MMinus       }
    "+"             { \p _ -> L (posn p) $ Op_Plus         }
    "-"             { \p _ -> L (posn p) $ Op_Minus        }
    "*"             { \p _ -> L (posn p) $ Op_Star         }
    "/"             { \p _ -> L (posn p) $ Op_Slash        }
    "&"             { \p _ -> L (posn p) $ Op_And          }
    "|"             { \p _ -> L (posn p) $ Op_Or           }
    "^"             { \p _ -> L (posn p) $ Op_Caret        }
    "%"             { \p _ -> L (posn p) $ Op_Percent      }
    "<<"            { \p _ -> L (posn p) $ Op_LShift       }
    ">>"            { \p _ -> L (posn p) $ Op_RShift       }
    ">>>"           { \p _ -> L (posn p) $ Op_RRShift      }
    "+="            { \p _ -> L (posn p) $ Op_PlusE        }
    "-="            { \p _ -> L (posn p) $ Op_MinusE       }
    "*="            { \p _ -> L (posn p) $ Op_StarE        }
    "/="            { \p _ -> L (posn p) $ Op_SlashE       }
    "&="            { \p _ -> L (posn p) $ Op_AndE         }
    "|="            { \p _ -> L (posn p) $ Op_OrE          }
    "^="            { \p _ -> L (posn p) $ Op_CaretE       }
    "%="            { \p _ -> L (posn p) $ Op_PercentE     }
    "<<="           { \p _ -> L (posn p) $ Op_LShiftE      }
    ">>="           { \p _ -> L (posn p) $ Op_RShiftE      }
    ">>>="          { \p _ -> L (posn p) $ Op_RRShiftE     }
    "@"             { \p _ -> L (posn p) $ Op_AtSign       }


{

pickyReadOct :: String -> Integer
pickyReadOct s =
  if not $ null remn
  then lexicalError $ "Non-octal digit '" ++ take 1 remn ++ "' in \"" ++ s ++ "\"."
  else n
    where (n,remn) = head $ readOct s

readHexExp :: (Eq a, Floating a) => String -> a
readHexExp s = let (m, suf) = head $ readHex s
                   (e, _) = case suf of
                             p:r | toLower p == 'p' -> head $ readHex r
                             _ -> (0, "")
                in m ** e

readCharTok :: String -> Char
readCharTok s = head . convChar . dropQuotes $ s
readStringTok :: String -> String
readStringTok = convChar . dropQuotes

dropQuotes :: String -> String
dropQuotes s = take (length s - 2) (tail s)

-- Converts a sequence of (unquoted) Java character literals, including
-- escapes, into the sequence of corresponding Chars. The calls to
-- 'lexicalError' double-check that this function is consistent with
-- the lexer rules for character and string literals. This function
-- could be expressed as another Alex lexer, but it's simple enough
-- to implement by hand.
convChar :: String -> String
convChar ('\\':'u':s@(d1:d2:d3:d4:s')) =
  -- TODO: this is the wrong place for handling unicode escapes
  -- according to the Java Language Specification. Unicode escapes can
  -- appear anywhere in the source text, and are best processed
  -- before lexing.
  if all isHexDigit [d1,d2,d3,d4]
  then toEnum (read ['0','x',d1,d2,d3,d4]):convChar s'
  else lexicalError $ "bad unicode escape \"\\u" ++ take 4 s ++ "\""
convChar ('\\':'u':s) =
  lexicalError $ "bad unicode escape \"\\u" ++ take 4 s ++ "\""
convChar ('\\':c:s) =
  if isOctDigit c
  then convOctal maxRemainingOctals
  else (case c of
          'b' -> '\b'
          'f' -> '\f'
          'n' -> '\n'
          'r' -> '\r'
          't' -> '\t'
          '\'' -> '\''
          '\\' -> '\\'
          '"' -> '"'
          _ -> badEscape):convChar s
  where maxRemainingOctals =
          if c <= '3' then 2 else 1
        convOctal n =
          let octals = takeWhile isOctDigit $ take n s
              noctals = length octals
              toChar = toEnum . fst . head . readOct
          in toChar (c:octals):convChar (drop noctals s)
        badEscape = lexicalError $ "bad escape \"\\" ++ c:"\""
convChar ("\\") =
  lexicalError "bad escape \"\\\""
convChar (x:s) = x:convChar s
convChar "" = ""

lexicalError :: String -> a
lexicalError = error . ("lexical error: " ++)

data L a = L Pos a
  deriving (Show, Eq)

-- (line, column)
type Pos = (Int, Int)

posn :: AlexPosn -> Pos
posn (AlexPn _ l c) = (l,c)

data Token
    -- Keywords
    = KW_Abstract
    | KW_Assert
    | KW_Boolean
    | KW_Break
    | KW_Byte
    | KW_Case
    | KW_Catch
    | KW_Char
    | KW_Class
    | KW_Const
    | KW_Continue
    | KW_Default
    | KW_Do
    | KW_Double
    | KW_Else
    | KW_Enum
    | KW_Extends
    | KW_Final
    | KW_Finally
    | KW_Float
    | KW_For
    | KW_Goto
    | KW_If
    | KW_Implements
    | KW_Import
    | KW_Instanceof
    | KW_Int
    | KW_Interface
    | KW_Long
    | KW_Native
    | KW_New
    | KW_Package
    | KW_Private
    | KW_Protected
    | KW_Public
    | KW_Return
    | KW_Short
    | KW_Static
    | KW_Strictfp
    | KW_Super
    | KW_Switch
    | KW_Synchronized
    | KW_This
    | KW_Throw
    | KW_Throws
    | KW_Transient
    | KW_Try
    | KW_Void
    | KW_Volatile
    | KW_While

    -- Separators
    | OpenParen
    | CloseParen
    | OpenSquare
    | CloseSquare
    | OpenCurly
    | CloseCurly
    | SemiColon
    | Comma
    | Period

    -- Literals
    | IntTok  Integer
    | LongTok Integer
    | DoubleTok Double
    | FloatTok Double
    | CharTok Char
    | StringTok String
    | BoolTok Bool
    | NullTok

    -- Identifiers
    | IdentTok String

    -- Operators
    | Op_Equal
    | Op_GThan
    | Op_LThan
    | Op_Bang
    | Op_Tilde
    | Op_Query
    | Op_Colon
    | Op_Equals
    | Op_LThanE
    | Op_GThanE
    | Op_BangE
    | Op_AAnd
    | Op_OOr
    | Op_PPlus
    | Op_MMinus
    | Op_Plus
    | Op_Minus
    | Op_Star
    | Op_Slash
    | Op_And
    | Op_Or
    | Op_Caret
    | Op_Percent
    | Op_LShift
    | Op_RShift
    | Op_RRShift
    | Op_PlusE
    | Op_MinusE
    | Op_StarE
    | Op_SlashE
    | Op_AndE
    | Op_OrE
    | Op_CaretE
    | Op_PercentE
    | Op_LShiftE
    | Op_RShiftE
    | Op_RRShiftE
    | Op_AtSign

-- Paragon
    | KW_P_Actor
    | KW_P_Close
    | KW_P_Lock
{-    | KW_P_Newactor -}
    | KW_P_Notnull
    | KW_P_Open
    | KW_P_Policy
    | KW_P_Policyof
    | KW_P_When
    | KW_P_Typemethod
    | KW_P_Readonly
    | KW_P_Reflexive
    | KW_P_Symmetric
    | KW_P_Transitive

--    | VarActorTok String

-- Anti-quasi-quotation
    | AntiQIdentTok String
    | AntiQNameTok  String
    | AntiQTypeTok  String
    | AntiQExpTok   String
  deriving (Show, Eq)

lexer :: String -> [L Token]
lexer = alexScanTokens

}
