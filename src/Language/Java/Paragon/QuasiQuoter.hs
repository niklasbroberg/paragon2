{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
module Language.Java.Paragon.QuasiQuoter where

--import Language.Haskell.TH.Syntax 

--import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lift
--import Language.Haskell.TH.Lib
import Language.Haskell.Meta.Parse

--import Data.Generics (extQ)
--import Data.Data

import Language.Java.Paragon.Parser
-- import Language.Java.Paragon.Syntax (ambName)
import Language.Java.Paragon.Lexer
import Language.Java.Paragon.Interaction

import Language.Java.Paragon.QuasiQuoter.Lift ()

import Prelude hiding(exp)

import Text.ParserCombinators.Parsec

quasiQuoterModule :: String
quasiQuoterModule = libraryBase ++ ".QuasiQuoter"


fromRight :: Either a b -> b
fromRight (Right res) = res
fromRight _ = panic (quasiQuoterModule ++ ".fromRight") ""


parserQQ :: (Lift a,Show a) => GenParser (L Token) () a -> QuasiQuoter
parserQQ f = QuasiQuoter{ 
               quoteExp  = lift . fromRight . parser f, 
               quotePat  = return .fromRight . parsePat .show . fromRight . parser f,
               quoteType = panic (quasiQuoterModule ++ ".parserQQ: quoteType") "",
               quoteDec  = panic (quasiQuoterModule ++ ".parserQQ: quoteDec" ) ""
             }       

nameQQ, expQQ, typeQQ, stmtQQ, lhsQQ :: QuasiQuoter
nameQQ = parserQQ name
expQQ  = parserQQ exp
typeQQ = parserQQ ttype          
stmtQQ = parserQQ stmt
lhsQQ  = parserQQ lhs

impDeclQQ,
  varDeclQQ, methodBodyQQ, memberDeclQQ, fieldDeclQQ, methodDeclQQ, 
  modifiersQQ, formalParamQQ, blockStmtQQ, classDeclQQ, lockPropQQ :: QuasiQuoter
varDeclQQ    = parserQQ varDecl
methodBodyQQ = parserQQ methodBody 
memberDeclQQ = parserQQ memberDecl
fieldDeclQQ  = parserQQ fieldDecl
methodDeclQQ = parserQQ methodDecl
modifiersQQ  = parserQQ (list modifier)
formalParamQQ = parserQQ formalParam
blockStmtQQ  = parserQQ blockStmt
classDeclQQ  = parserQQ classDecl
lockPropQQ   = parserQQ lockProperties
impDeclQQ    = parserQQ importDecl
