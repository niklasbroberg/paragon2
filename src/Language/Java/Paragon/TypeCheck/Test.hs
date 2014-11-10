module Language.Java.Paragon.TypeCheck.Test where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Parser

import Language.Java.Paragon.TypeCheck.TcExp
import Language.Java.Paragon.TypeCheck.Monad
import Language.Java.Paragon.TypeCheck.TcEnv
import Language.Java.Paragon.TypeCheck.TcState
import Language.Java.Paragon.TypeCheck.Policy
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.Locks



import qualified Data.Map as Map

testExp :: String -> IO ()
testExp str =
  case parser stmtExp str of
   Right e -> do res <- runTc testEnv testState $ tcExp e
                 print res
   Left errs -> print errs

testState :: TcState
testState = TcState {
              actors = Map.empty,
              lockMods = noMods,
              exnS = Map.empty
            }

testEnv :: TcEnv
testEnv = TcEnv {
            typemap = testTypes,
            vars = Map.fromList
                    [(nam "x", vti intT top)],
            lockstate = [],
            returnI = (intT, bottom),
            exnsE = Map.empty,
            branchPCE = (Map.empty, bottom)
          }

vti t p = VTI t p False False

testTypes :: TypeMap
testTypes = TypeMap {
              this = clsType (Ident "This"),
              fields = Map.empty,
              methods = Map.fromList 
                         [((nam "foo", [intT]), fooInfo)],
              constrs = Map.fromList
                         [((TcClassT [(Ident "Foo", [])], []), cInfo1),
                          ((TcClassT [(Ident "Foo", [])], [intT]), cInfo2)],
              locks = Map.fromList [(nam "L", lInfo)],
              policies = Map.empty,
              typemethods = Map.empty,
              types = Map.empty
            }


fooInfo :: MTypeInfo
fooInfo = MTI {
            mRetType = intT,
            mRetPol  = bottom,
            mPars    = [bottom],
            mWrites  = top,
            mExpects = [],
            mLMods   = noMods,
            mExns    = []
          }

cInfo1, cInfo2 :: CTypeInfo
cInfo1 = CTI {
           cPars = [],
           cWrites = top,
           cExpects = [],
           cLMods = noMods,
           cExns = []
         }

cInfo2 = cInfo1 { cPars = [bottom] }

lInfo :: LTypeInfo
lInfo = LTI { arity = 1, lockPol = top }

nam :: String -> Name
nam str = Name [Ident str]