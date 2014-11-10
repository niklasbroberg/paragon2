module Language.Java.Paragon.TypeCheck.Evaluate where

-- Compile-time evaluation of code


import Language.Java.Paragon.Syntax
--import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.TypeCheck.Monad
import Language.Java.Paragon.TypeCheck.Policy
--import Language.Java.Paragon.TypeCheck.TcExp
--import Language.Java.Paragon.TypeCheck.TcEnv
--import Language.Java.Paragon.TypeCheck.TcState

--import Control.Applicative ((<$>))
--import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

evaluateModule :: String
evaluateModule = typeCheckerBase ++ ".Evaluate"

--------------------------------------------
--       Working with typemethods         --
--------------------------------------------
{-
readPol :: [Modifier] -> Tc r (Maybe TcPolicy)
readPol ms = do
  let rs = [ p | Reads p <- ms ]
  case rs of
   [] -> return Nothing
   [p] -> Just <$> evaluate p
   _ -> fail "More than one read modifier found"

fieldPol, localVarPol :: [Modifier] -> Tc r TcPolicy
fieldPol ms = do
  mpol <- readPol ms
  return $ mpol `orUse` bottom

paramPol :: Ident -> [Modifier] -> Tc r TcPolicy
paramPol i ms = do
  mpol <- readPol ms
  case mpol of
    Nothing -> return $ TcRigidVar i
    Just p -> return p

localVarPol ms = do
  mpol <- readPol ms
  case mpol of
    Nothing -> newMetaPolVar
    Just p -> return p

returnPol :: [Modifier] -> [TcPolicy] -> Tc r TcPolicy
returnPol ms ppols = do
  mpol <- readPol ms
  let def = foldl join bottom ppols
  return $ mpol `orUse` def
-}
evaluate :: Policy SourcePos -> TcDeclM (PrgPolicy TcActor)
evaluate = evalPolicy
{-evaluate (PolicyExp _ pe) = evalPolicyExp pe
evaluate (ExpName _ n) = -- getPolicy n
--  polMap <- (policies . typemap) <$> getEnv
--  case Map.lookup n polMap of
--    Nothing -> fail $ "Unknown policy: " ++ prettyPrint n
--    Just p -> return p
evaluate (BinOp _ p1 (Add _) p2) = do
  pol1 <- evaluate p1
  pol2 <- evaluate p2
  return $ pol1 `meet` pol2
evaluate (BinOp _ p1 (Mult _) p2) = do
  pol1 <- evaluate p1
  pol2 <- evaluate p2
  return $ pol1 `join` pol2
evaluate (MethodInv _ mi) = evalTypeMethod mi
evaluate e = fail $ "Unsupported type-level expression: " ++ prettyPrint e
-}
evalTypeMethod :: MethodInvocation SourcePos -> TcDeclM (TcPolicy TcActor)
evalTypeMethod = panic (evaluateModule ++ ".evalTypeMethod") ("undefined!")

orUse :: Maybe a -> a -> a
orUse = flip fromMaybe


isFinal :: [Modifier SourcePos] -> Bool
isFinal = (Final defaultPos `elem`)
