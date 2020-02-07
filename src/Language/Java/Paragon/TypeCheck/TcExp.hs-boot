{-# LANGUAGE PatternGuards, BangPatterns #-}
-- | Module for typechecking expressions.
module Language.Java.Paragon.TypeCheck.TcExp where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.Error
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.TypeCheck.Policy
import Language.Java.Paragon.TypeCheck.Actors
import Language.Java.Paragon.TypeCheck.Locks
import Language.Java.Paragon.TypeCheck.Monad
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.TypeMap
import Language.Java.Paragon.TypeCheck.NullAnalysis

import Data.List ((\\))
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Control.Applicative ((<$>))
import Control.Monad (when, foldM)

import qualified Data.ByteString.Char8 as B ()
{-
tcExpModule :: String
tcExpModule = typeCheckerBase ++ ".TcExp"

--import qualified Data.Map as Map
-----------------------------------
--    Types of literal values    --
-----------------------------------

litType :: Literal SourcePos -> TcType
litType (Int     _ _) = intT
litType (Word    _ _) = longT
litType (Float   _ _) = floatT
litType (Double  _ _) = doubleT
litType (Boolean _ _) = booleanT
litType (Char    _ _) = charT
litType (String  _ _) = clsTypeToType stringT
litType (Null    _  ) = nullT

-----------------------------------
--    Checking expressions       --
-----------------------------------}

-- | Typechecks a term that is parsed as some expression and returns a triple
-- consisting of the (state) type of that expression, the policy on the
-- expression, and a typechecked expression.
-- Encapsulated in the TcCodeM monad gives access to the code environment,
-- state, allows it to fail, add error messages and policy contraints.  
tcExp :: Exp SourcePos -> TcCodeM (TcStateType, ActorPolicy, Exp T)
{-
-- Rule PAREN
-- Expressions in parantheses are simply relayed
tcExp (Paren _ e) = do (ty, p, e') <- tcExp e
                       return (ty, p, Paren (toT ty) e')
                       
-- Rule LIT
-- Literals simply look up their state type. Their policy defaults to bottom
-- (we might eventually want to infer the appropriate policy instead).
tcExp (Lit _ l) = do
  sty <- getStateType Nothing Nothing $ litType l 
  return (sty, bottom, Lit (toT sty) (notAppl l))

-- Rule THIS
-- Simple wrapping, policy defaults to bottom.
tcExp (This _) = do
  tTy <- getThisStateType
  return (tTy, bottom, This $ toT tTy)

-- Rule BINOP
-- Any binary operation consists of checking the two sub-expressions and
-- joining the policies of each.
tcExp (BinOp _ e1 op e2) = do
  (ty1, p1, e1') <- tcExp e1
  (ty2, p2, e2') <- tcExp e2
  tyRes <- opType op ty1 ty2
  return (tyRes, p1 `join` p2, BinOp (toT tyRes) e1' (notAppl op) e2')

-- Rule VAR/FIELD
-- If we have a regular variable / field we simply look up its type and policy.
-- If we have a lock we additionaly check its arity. If we do now know if it is
-- a lock or not, we try assuming it is a lock first.
tcExp (ExpName _ n) = do
    debugPrint $ "tcExp[Var/Field]: " ++ show n
    case n of
      Name _ EName mPre i -> do
             (ty, pol, _) <- lookupVar mPre i
             return (ty, pol, ExpName (toT ty) (notAppl n))
      Name sp LName mPre i -> do
             LSig pL arL _ <- lookupLock mPre i
             check (arL == 0) $
               mkError (LArityMismatch (prettyPrint n) arL 0) sp
             let ty = lockT [TcLock n []]
             return $ (ty, pL, ExpName (toT ty) (notAppl n))
      Name sp EOrLName mPre i -> do
             tryCatch (tcExp $ ExpName sp $ Name sp LName mPre i)
                (\ec ->tcExp $ ExpName sp $ Name sp EName mPre i)
             
      _ -> panic (tcExpModule ++ ".tcExp:ExpName")
           $ "Unexpected name: " ++ show n
  
-- Rule VARASS/FIELDASS
-- Fairly extensive check. We first check the left-hand side (lhs) of the
-- assignment to see if the location exists and if it is allowed to be updated
-- in the current context.
-- We then continue to check the assignment itself to see if the there are any
-- policy violations.
tcExp ex@(Assign exSp lhs _op rhs) = do
  debugPrint $ "\n##   " ++ prettyPrint ex ++ "    ##\n"
  -- Checking the left hand side, gives us:
  (tyV,    -- type of the lhs variable/field
   pV,     -- policy of the lhs
   mEnt,   -- ?; used for branch pc check..
   mNStab, -- is final(ized)
   nnf,    -- non-null field
   lhs'    -- type-checked lhs
   ) <- 
    case lhs of
      -- Named LHS
      NameLhs sp n@(Name _ EName mPre iF@(Ident spF _)) ->  do
          case mPre of
            Nothing -> do -- VARASS
                (tyV, pV, _) <- lookupVar Nothing iF
                return (unStateType tyV, pV, Just (varE n), Just (n, True), False,
                                    NameLhs (toT tyV) (notAppl n))
            Just pre -> do -- FIELDASS
                (Just tyO, tmO, pO) <- lookupPrefixName pre
                case Map.lookup (unIdent iF) $ fields tmO of
                  Just (VSig tyF pF _ _ fin nnf) -> do
                     -- field policy cannot be lrt object policy
                     constraint [] pO pF $ 
                       mkError (FieldLRTObject (prettyPrint iF) (prettyPrint pre) 
                         (prettyPrint pO) (prettyPrint pF)) sp 
                     return (tyF, pF, Just (varE n), Just (n, fin), nnf, 
                                NameLhs (Just (tyF, False)) (notAppl n))
                  Nothing -> failE $ -- field not found
                    mkError (NoSuchField (prettyPrint pre) (prettyPrint tyO)
                      (prettyPrint iF)) spF
      NameLhs _ n -> panic (tcExpModule ++ ".tcEcp:Assign")
                     $ "NameLhs not an EName: " ++ show n

      -- Own field LHS
      FieldLhs sp (PrimaryFieldAccess _ e fi) -> do
            (tyE, pE, e') <- tcExp e
            (VSig tyF pF _ _ _ nnf) <- lookupFieldT tyE fi
            let eEnt = case e of
                         This _ -> Just $ thisFE $ unIdent fi
                         _ -> Nothing
            -- field policy cannot be lrt object policy
            constraint [] pE pF $ mkError
              (FieldLRTObject (prettyPrint fi) (prettyPrint e) (prettyPrint pE)
                (prettyPrint pF)) sp
            return (tyF, pF, eEnt, Nothing, nnf,
                       FieldLhs (Just (tyF, False)) 
                                (PrimaryFieldAccess (Just (tyF, False)) 
                                                    e' 
                                                    (notAppl fi)))

      -- Array element LHS
      ArrayLhs sp (ArrayIndex _ arrE iE) -> do
            (tyA, pA, arrE') <- tcExp arrE
            case unStateType tyA of
              TcRefT (TcArrayT tyElem pElem) -> do
                (tyI, pI, iE') <- tcExp iE
                -- array index has to be an integer
                check (isIntConvertible tyI) $ mkError 
                  (NonIntIndex (prettyPrint tyI)) sp
                -- index policy has to be lrt array policy
                constraintLS pI pA $ mkError
                  (ArrayLRTIndex (prettyPrint arrE) (prettyPrint pA)
                                 (prettyPrint iE)   (prettyPrint pI))
                  sp
                -- array policy has to be lrt new element policy
                constraint [] pA pElem $ mkError
                  (ExprLRTArray (prettyPrint arrE) (prettyPrint pA)
                                (prettyPrint pElem)) 
                  sp 
                return (tyElem, pElem, Nothing, Nothing, False,
                        ArrayLhs (Just (tyElem, False)) 
                                 (ArrayIndex (Just (tyElem, False)) arrE' iE'))

              _ -> failE $ mkError -- is not an array
                  (NonArrayIndexed (prettyPrint arrE) (prettyPrint tyA))
                  sp

      -- Unsupported LHS
      _ -> failE $ mkError (NotSupported "left-hand side" (prettyPrint lhs))
                           exSp

  (tyRhs, pRhs, rhs') <- tcExp rhs

  -- Check all the necessary constraints:
  -- do not assign possible null value to non-nullable location
  check (not (nnf && (nullableFromStateType tyRhs))) $ mkError
    (NNFieldAssN (prettyPrint lhs) (prettyPrint rhs)) exSp
  
  -- TODO: Check that _op is allowed on tyV
  mps <- tyV =<: tyRhs
  case mps of
    -- policy type paramters do not match in arity
    Nothing -> failE $ mkError (TypeMismatch (prettyPrint (unStateType tyRhs))
                                             (prettyPrint tyV))
                               exSp
    Just ps -> do
      -- Check: parameter-policies are equivalanet
      mapM_ (\(p,q) -> do
               constraint [] p q $ mkError (UnificationFailed "assignment") 
                                           exSp
               constraint [] q p $ mkError (UnificationFailed "assignment")
                                           exSp
            ) ps

      -- Check: E[branchPC](n) <= pV
      bpcs <- maybe getBranchPC_ getBranchPC mEnt
      constraintPC bpcs pV $ \p src -> mkError (WriteBounded (prettyPrint lhs)
           (prettyPrint pV) src (prettyPrint p)) exSp
      -- Check: exnPC(S) <= pV
      epcs <- getExnPC
      constraintPC epcs pV $ \p src -> mkError (WriteBounded (prettyPrint lhs)
           (prettyPrint pV) src (prettyPrint p)) exSp
      -- Check: pRhs <= pV modulo L
      constraintLS pRhs pV $ mkError
        (PolViolatedAss (prettyPrint rhs) (prettyPrint pRhs) 
                        (prettyPrint lhs) (prettyPrint pV)) exSp
      -- Check: pO <= pV, if pO exists
      --  maybeM mpO (\pO -> constraint [] pO pV $
      --           "When changing the state of an object, the policy of the changed field may not " ++
      --             "be less restrictive than the policy of the object\n" ++
      --             "

      styV <- updateStateType mNStab tyV (Just tyRhs)
      debugPrint $ "Done with assignment"

      return (styV, pV, Assign (Just (tyV, False)) lhs' (notAppl _op) rhs')

-- Rule CALL
-- Redirected into separate function
tcExp (MethodInv _ mi) = do
  (ty, p, mi') <- tcMethodOrLockInv mi
  return (ty, p, MethodInv (toT ty) mi')

-- Rule NEW
-- Redirected into separate function
tcExp (InstanceCreation _ tas ct args Nothing) = do
  tyT <- evalSrcClsType genBot ct
  (sty, p, args', isN) <- tcCreate tyT tas args
  return (sty, p, InstanceCreation (setNative isN $ toT sty) (map notAppl tas)
                                   (notAppl ct) args' Nothing)

-- Rule COND
-- Recursively check the branches (with increased pc) and check if types of
-- branches match.
tcExp (Cond sp c e1 e2) = do
  (tyC, pC, c') <- tcExp c
  -- condition has to be a boolean
  check (isBoolConvertible tyC) $ mkError
    (CondNotBool (prettyPrint tyC)) sp
  -- TODO, replace branch PC info with proper error and source location
  extendBranchPC pC ("conditional expression dependent on expression " 
                     ++ prettyPrint c) $ do
    -- typecheck branches
    ((ty1, p1, e1'), (ty2, p2, e2')) <- 
        (   isNotNullChecked c 
         >> (maybeM (mLocks tyC) (\ls -> applyLockMods ([], ls)))
         >> tcExp e1) ||| (isNullChecked c >> tcExp e2)
    -- result of each branch has to be equal
    check (ty1 == ty2
           || isNullType ty1 && isRefType ty2
           || isNullType ty2 && isRefType ty1) $ 
      mkError BranchTypeMismatch sp
    
    return (ty1, pC `join` p1 `join` p2, Cond (toT ty1) c' e1' e2')

-- Rule POLICYEXP
-- Redirected into separate function
tcExp (PolicyExp _ pl) = do
  pRep <- tcPolicyExp pl
  let ty = policyPolT $ KnownPolicy $ RealPolicy pRep
  return (ty, bottom, PolicyExp (toT ty) (notAppl pl))

-- Rule POST/PRE-INCREMENT/DECREMENT
-- Basically only check that operator is used on numeric type
tcExp (PostIncrement sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isNumConvertible tyE) $ mkError 
    (OpNotNumeric "Post-increment" (prettyPrint tyE)) sp
  return (tyE, pE, PostIncrement (toT tyE) e')
tcExp (PostDecrement sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isNumConvertible tyE) $ mkError
    (OpNotNumeric "Post-decrement" (prettyPrint tyE)) sp
  return (tyE, pE, PostDecrement (toT tyE) e')
tcExp (PreIncrement sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isNumConvertible tyE) $ mkError
    (OpNotNumeric "Pre-increment" (prettyPrint tyE)) sp
  return (tyE, pE, PreIncrement (toT tyE) e')
tcExp (PreDecrement sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isNumConvertible tyE) $ mkError
    (OpNotNumeric "Pre-decrement" (prettyPrint tyE)) sp
  return (tyE, pE, PreDecrement (toT tyE) e')

-- Rule PREP
-- Other unary operators.
-- All just check if operator is applied on correct type, except cast.
tcExp (PrePlus sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isNumConvertible tyE) $ mkError
    (OpNotNumeric "Pre-plus" (prettyPrint tyE)) sp
  let ty = unaryNumPromote_ tyE
  return (ty, pE, PrePlus (toT ty) e')
tcExp (PreMinus sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isNumConvertible tyE) $ mkError
    (OpNotNumeric "Pre-minus" (prettyPrint tyE)) sp
  let ty = unaryNumPromote_ tyE
  return (ty, pE, PreMinus (toT ty) e')
tcExp (PreBitCompl sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isIntConvertible tyE) $ mkError
    (OpNotIntegral "Pre-complement bit" (prettyPrint tyE)) sp
  let ty = unaryNumPromote_ tyE
  return (ty, pE, PreBitCompl (toT ty) e')
tcExp (PreNot sp e) = do
  (tyE, pE, e') <- tcExp e
  check (isBoolConvertible tyE) $ mkError 
    (OpNotBoolean "Pre-complement boolean" (prettyPrint tyE)) sp
  return (stateType booleanT, pE, PreNot (Just (booleanT, False)) e')
tcExp (Cast sp t e) = do
  (tyE, pE, e') <- tcExp e
  tyC <- evalSrcType genBot t
  (mps, canExn) <- tyC <<: tyE
  case mps of
    -- policy parameters should be of same arity and equivalent
    Nothing -> failE (mkError WrongCastT sp)
    Just ps -> do
        mapM_ (\(p,q) -> do
                 constraint [] p q (mkError (UnificationFailed "cast") sp)
                 constraint [] q p (mkError (UnificationFailed "cast") sp)
              ) ps

        when (canExn) $ -- TODO: could throw ClassCastException
               return ()
        -- update new state type information
        styC <- updateStateType Nothing tyC (Just tyE)
        return (styC, pE, Cast (Just (tyC, False)) (notAppl t) e')

-- Rule FIELDACCESS
-- Redirected into separate function
tcExp (FieldAccess _ fa) = do
  (ty, p, fa') <- tcFieldAccess fa
  return (ty, p, FieldAccess (toT ty) fa')

-- Arrays

-- Rule ARRAYCREATE
tcExp (ArrayCreate sp bt dimEsPs dimImplPs) = do
  baseTy <- evalSrcType genMeta bt

  -- Check the types and policies of all dimension expressions
  check (not $ null dimEsPs) $ mkError ArrayZeroDim sp
  -- At least one dimension exists:
  let ((dimE1,mDimP1):dimEsPsRest) = dimEsPs

  -- The first dimexpr will determine the policy
  -- of the whole array creation expression
  (ty1, pol1, dimE1') <- tcExp dimE1
  -- Dimexprs must have integral-convertible types
  check (isIntConvertible ty1) $ mkError (NonIntDimArray (prettyPrint ty1)) sp

  -- Check that the remaining dimexprs each conform to
  -- the policy given at the level outside it
  (polEDims, dimEsRest) <- checkDimExprs [] [] dimEsPsRest sp
                             =<< (evalMaybePol mDimP1)

  -- Evaluate given policies for implicit dimensions
  polIDims <- mapM evalMaybePol dimImplPs

  -- Return the array type, and the policy of the outermost dimexpr
  let ty         = mkArrayType baseTy $ (polEDims ++ polIDims)
      dimPs'     = map (fmap notAppl) $ snd $ unzip dimEsPs
      dimEsPs'   = zip (dimE1':dimEsRest) dimPs'
      dimImplPs' = map (fmap notAppl) dimImplPs
  return (stateType ty, pol1, 
            ArrayCreate (Just (ty, False)) (notAppl bt) dimEsPs' dimImplPs')

      where checkDimExprs :: [ActorPolicy]   -- ^ Policies of earlier dimensions
                          -> [Exp T]         -- ^ Annotated expressions
                          -> [(Exp SourcePos, Maybe (Policy SourcePos))] 
                                             -- ^ Remaining dimexprs/pols
                          -> SourcePos       -- ^ Source location
                          -> ActorPolicy     -- ^ Policy of previous dimension
                          -> TcCodeM ([ActorPolicy], [Exp T])
            checkDimExprs accP accE [] _ pPrev = 
              return $ (reverse (pPrev:accP), reverse accE)
            checkDimExprs accP accE ((e,mp):emps) spos pPrev =
              do (tyE,pE,e') <- tcExp e
                 check (isIntConvertible tyE) $
                   mkError (NonIntDimArray (prettyPrint tyE)) spos
                 -- Each dimexpr must satisfy the policy of the outer dim
                 constraintLS pE pPrev $
                   mkError (ArrayDimPol (prettyPrint e) (prettyPrint pE) 
                     (prettyPrint pPrev)) spos
                 pNext <- evalMaybePol mp
                 checkDimExprs (pPrev:accP) (e':accE) emps spos pNext

-- Rule ARRAYCREATEINIT
tcExp (ArrayCreateInit _ bt dimImplPs arrInit) = do
  baseTy <- evalSrcType genMeta bt
  -- Evaluate given policies for implicit (all) dimensions
  dimPols <- mapM evalMaybePol dimImplPs
  -- Check that the initializer has the right type and policies
  -- of subexpressions
  arrInit' <- tcArrayInit baseTy dimPols arrInit

  -- Return the specified array type
  -- Literal array initializers have known length, 
  -- so their apparent policy is bottom
  let ty = mkArrayType baseTy dimPols
  return (stateType ty, bottom, 
            ArrayCreateInit (Just (ty, False)) (notAppl bt) 
                            (map (fmap notAppl) dimImplPs) arrInit')

-- Rule ARRAYACCESS
tcExp (ArrayAccess spA (ArrayIndex spI arrE iE)) = do
  (tyA, pA, arrE') <- tcExp arrE
  case unStateType tyA of
    TcRefT (TcArrayT tyElem pElem) -> do
      (tyI, pI, iE') <- tcExp iE
      check (isIntConvertible tyI) $ mkError (NonIntIndex (prettyPrint tyI)) spI
      styElem <- getStateType Nothing Nothing tyElem
      return (styElem, pElem `join` pA `join` pI, 
                    ArrayAccess (Just (tyElem, False)) 
                                (ArrayIndex (Just (tyElem, False)) arrE' iE'))

    _ -> failE $ mkError (NonArrayIndexed (prettyPrint arrE) (prettyPrint tyA))
                         spA  

-- Unsupported expressions
tcExp e = failE $ mkError (NotSupported "expression" (prettyPrint e)) defaultPos 
 -- TODO derivie position from expression...

--------------------------
-- Array initializers

tcArrayInit :: TcType -> [ActorPolicy] -> TypeCheck TcCodeM ArrayInit
tcArrayInit baseType (pol1:pols) (ArrayInit sp inits) = do
  (ps, inits') <- unzip <$> mapM (tcVarInit baseType pols) inits
  mapM_ (\(p,e) -> constraintLS p pol1 $ mkError
         (ArrayInitExpPol (prettyPrint e) (prettyPrint p) (prettyPrint pol1)) sp
        ) (zip ps inits)
  return $ ArrayInit Nothing inits'
tcArrayInit _ [] _ = fail $ "Array initializer has too many dimensions"

tcVarInit :: TcType -> [ActorPolicy] -> VarInit SourcePos -> TcCodeM (ActorPolicy, VarInit T)
tcVarInit baseType pols (InitExp _ e) = do
--  debugPrint $ "Pols: " ++ show pols
--  debugPrint $ "Exp:  " ++ show e
  (tyE,pE,e') <- tcExp e
  let elemType = stateType $ mkArrayType baseType pols
  check (tyE == elemType) $  toUndef $ 
            "Expression " ++ prettyPrint e 
            ++ " in array initializer has type " ++ prettyPrint tyE
            ++ " but array expects elements of type " ++ prettyPrint elemType
  return (pE, InitExp Nothing e')
tcVarInit baseType pols (InitArray _ arr) = do 
  arr' <- tcArrayInit baseType pols arr
  return (bottom, InitArray Nothing arr')

evalMaybePol :: Maybe (Policy SourcePos) -> TcCodeM ActorPolicy
evalMaybePol = maybe genMeta ((RealPolicy <$>) . evalPolicy)

--------------------------
-- Field Access

tcFieldAccess :: FieldAccess SourcePos -> TcCodeM (TcStateType, ActorPolicy, FieldAccess T)
tcFieldAccess (PrimaryFieldAccess _ e fi) = do
  (tyE,pE,e') <- tcExp e
  VSig tyF pFi _ _ _ _ <- instThis pE <$> lookupFieldT tyE fi
  styF <- getStateType Nothing Nothing tyF -- TODO: this?
  return (styF, pE `join` pFi, PrimaryFieldAccess (toT styF) e' (notAppl fi))

tcFieldAccess fa = error $ "Unsupported field access: " ++ prettyPrint fa

--------------------------
-- Instance creation

tcCreate :: TcClassType -> [TypeArgument SourcePos] -> [Argument SourcePos] 
         -> TcCodeM (TcStateType, ActorPolicy, [Argument T],Bool)
tcCreate ctyT@(TcClassT tyN@(Name _ _ _ tyI) _) tas args = do
  resP <- newMetaPolVar tyI
  (tysArgs, psArgs, args') <- unzip3 <$> mapM tcExp args
  (tps,iaps,genCti) <- lookupConstr ctyT tas resP (map unStateType tysArgs) psArgs
  -- TODO: Check that the arguments in tyT
  --       match those expected by the type
  -- TODO: Type argument inference
  check (length tps == length tas) $ toUndef $
        "Wrong number of type arguments in instance creation expression.\n" ++
        "Constructor expects " ++ show (length tps) ++ 
        " arguments but has been given " ++ show (length tas)
  tArgs <- mapM (uncurry $ evalSrcTypeArg genBot) (zip tps tas)
  iaas  <- mapM (instanceActorId . Name defaultPos EName (Just tyN) . (\s -> Ident defaultPos s)) iaps
  let itps = map (ActorParam defaultPos . (\s -> Ident defaultPos s)) iaps
      itas = map TcActualActor iaas
      
 -- tm <- getTypeMap
  let cti = instThis resP $ instantiate (zip (tps++itps) (tArgs++itas)) genCti
      (CSig psIs psPars pW lExp lMods exns nnps isNative) = cti

  -- Check argument's null type
  let nts = map nullFromStateType tysArgs
  let toCheck = [(p, nt, arg) | nnp <- nnps, (p, Just nt, arg) <- zip3 psIs nts args, nnp == p]
  mapM_ (\(p,nt,arg) -> check (not $ nullable nt) $ toUndef $
                    "When calling constructor " ++ prettyPrint ctyT ++ ":\n" ++
                    "Parameter: " ++ prettyPrint p ++ " is not allowed to be null while\n" ++
                    "Expression: " ++ prettyPrint arg ++ " can't be assumed such as."
        ) toCheck
  -- Check lockstates
  l <- getCurrentLockState
  check (null (lExp \\ l)) $ toUndef $ 
            "Lockstate too weak when calling constructor " ++ prettyPrint ctyT ++ ":\n" ++ 
            "Required lock state: " ++ prettyPrint lExp ++ "\n" ++
            "Current lock state: " ++ prettyPrint l
  -- Check argument constraints
  let subst = zip psIs psArgs
      (pW':psPars') = map (substParPols subst) (pW:psPars)
      (exnPs, _exnAcs) = 
          unzip [ ((t, (rX', wX')),  (ExnType t, (wX', modsX))) |
                  (t, ExnSig rX wX modsX) <- exns,
                  let rX' = substParPols subst rX, 
                  let wX' = substParPols subst wX 
                ]
  mapM_ (\(arg,argP,parP) -> 
             constraintLS argP parP $ toUndef $
                 "Constructor applied to argument with too restrictive policy:\n" ++ 
                 "Constructor: " ++ prettyPrint ctyT ++ "\n" ++
                 "Argument: " ++ prettyPrint arg ++ "\n" ++
                 "  with policy: " ++ prettyPrint argP ++ "\n" ++
                 "Declared policy bound: " ++ prettyPrint parP
        ) (zip3 args psArgs psPars')
  -- Check E[branchPC](*) <= pW
  bpcs <- getBranchPC_
  constraintPC bpcs pW' $ \p src -> toUndef $
       "Constructor " ++ prettyPrint ctyT ++ 
       " with declared write effect " ++ prettyPrint pW' ++
       " not allowed in " ++ src ++
       " with write effect bound " ++ prettyPrint p
  -- Check exnPC(S) <= pW
  epc <- getExnPC
  constraintPC epc pW' $ \p src -> toUndef $
      "Constructor " ++ prettyPrint ctyT ++ 
      " with declared write effect " ++ prettyPrint pW' ++
      " not allowed in " ++ src ++
      " with write effect bound " ++ prettyPrint p
  -- Check Exns(X)[write] <= E[exns](X)[write] AND
  -- Check Exns(X)[read]  >= E[exns](X)[read]  
  mapM_ (uncurry $ exnConsistent (Right ctyT)) exnPs

  -- Fix outgoing state
--  activateExns exnAcs    -- ==> S' = Sn[exns{X +-> (Sx, exns(X)[write])}]
  applyLockMods lMods    -- ==> S'' = S'[lockMods ||>>= lMods, 
--  scrambleState          -- ==>          state scrambled]
  -- Committed computation
  k <- foldM (\b e -> do
                (st, _, _) <- tcExp e
                case st of
                  (TcInstance _ _ nt) -> return $ b && (committed nt)
                  (TcType _ nt)       -> return $ b && (committed nt)
                  _                   -> panic "CommittedSt called on Actor, Lock or Policy" ""
             ) True args
  let nt = case k of
             True  -> Committed
             False -> Free
  styT <- getStateType Nothing Nothing $ clsTypeToType ctyT
  let styT' = setNullInStateType styT (NotNull, nt)
  return (styT', resP, args', isNative)
tcCreate _ _ _ = panic (tcExpModule ++ ".tcCreate")
                 $ "AntiQName"

--------------------------
-- Method invocations

-- | Check a method invocation, which could possibly represent
--   a lock query expression.
tcMethodOrLockInv :: MethodInvocation SourcePos -> TcCodeM (TcStateType, ActorPolicy, MethodInvocation T)
tcMethodOrLockInv (MethodCallOrLockQuery spM (Name spN MOrLName mPre i) args) = do
  -- We couldn't resolve without type information whether
  -- this truly is a method or a lock.
  baseTm <- getTypeMap
  preTm <- case mPre of
             Nothing -> return baseTm
             Just pre -> do
                       (_, preTm, _) <- lookupPrefixName pre
                       return preTm
  let nt = case Map.lookup (unIdent i) $ locks preTm of
             Just _  -> LName
             Nothing -> MName
  tcMethodOrLockInv (MethodCallOrLockQuery spM (Name spN nt mPre i) args)

tcMethodOrLockInv (MethodCallOrLockQuery _ nam@(Name _ LName mPre i) args) = do
  -- This is a lock query
  LSig pL arL _ <- lookupLock mPre i
  check (arL == length args) $ toUndef $
            "Lock " ++ prettyPrint nam ++ " expects " ++ show arL
            ++ " arguments but has been given " ++ show (length args)

  (tysArgs, psArgs, args') <- unzip3 <$> mapM tcExp args
  -- debugPrint $ "args': " ++ show args'
  mapM_ (\ty -> check (isActorType ty) $ toUndef $
                 "Trying to query lock with argument of type " 
                ++ prettyPrint ty ++ "\n" ++
                       "All arguments to lock query must be of type actor") tysArgs
  let tyR = lockT [TcLock nam $ map (fromJust . mActorId) tysArgs]
  -- debugPrint $ "tyR: " ++ show tyR
  return (tyR, foldl1 join (pL:psArgs),
             MethodCallOrLockQuery (toT tyR) (notAppl nam) args')
      
tcMethodOrLockInv mi = tcMethodInv mi

-- | Check a true method invocation
tcMethodInv :: MethodInvocation SourcePos -> TcCodeM (TcStateType, ActorPolicy, MethodInvocation T)
tcMethodInv mi = do
  -- debugPrint $ "tcMethodInv: " ++ prettyPrint mi
  (n, msig, args, psArgs, pE, ef, tysArgs) <-
      case mi of 
        MethodCallOrLockQuery _ n@(Name _ MName mPre i) args -> do
            -- This is a true method call
            (tysArgs, psArgs, args') <- unzip3 <$> mapM tcExp args
            (pPath, tps, msig) <- lookupMethod mPre i [] (map unStateType tysArgs) psArgs
            -- debugPrint $ "msig: " ++ prettyPrint msig
            check (null tps) $ toUndef $
                  "Method " ++ prettyPrint i ++ " expects " ++
                  show (length tps) ++ " type arguments but has been given 0"
            return $ (n, msig, args, psArgs, pPath, 
                           \ty -> MethodCallOrLockQuery (toT ty) (notAppl n) args', tysArgs)
        MethodCallOrLockQuery _ n _ -> panic (tcExpModule ++ ".tcMethodInv")
                            $ "Unexpected name: " ++ show n
        PrimaryMethodCall _ e tas i args -> do
            debugPrint $ "---- " ++ prettyPrint i ++ " ----"
            debugPrint $ "Type arguments: " ++ show tas
            (tyE, pE, e') <- tcExp e
            (tysArgs, psArgs, args') <- unzip3 <$> mapM tcExp args
            let tas' = map (ActualArg defaultPos) tas
            (tps, genMSig) <- instThis pE <$> 
                              lookupMethodT tyE i tas' (map unStateType tysArgs) psArgs
            tArgs <- mapM (uncurry $ evalSrcTypeArg genBot) $ 
                                     zip tps tas'
            let msig = instantiate (zip tps tArgs) genMSig
            return $ (mkSimpleName MName i, msig, args, psArgs, pE,
                      \ty -> PrimaryMethodCall (toT ty) e' (map notAppl tas) (notAppl i) args', tysArgs)
        TypeMethodCall _ n tas i args -> do
            (tysArgs, psArgs, args') <- unzip3 <$> mapM tcExp args
            let tas' = map (ActualArg defaultPos) tas
            (pPath, tps, genMSig) <- lookupMethod (Just n) i tas' (map unStateType tysArgs) psArgs
            check (length tps == length tas) $ toUndef $
                  "Method " ++ prettyPrint i ++ " expects " ++
                  show (length tps) ++ " type arguments but has been\
                  \ given " ++ show (length tas)
            tArgs <- mapM (uncurry $ evalSrcTypeArg genBot) $ 
                                     zip tps tas'
            let msig = instantiate (zip tps tArgs) genMSig
            return $ (n, msig, args, psArgs, pPath, 
                      \ty -> TypeMethodCall (toT ty) (notAppl n) 
                             (map notAppl tas) (notAppl i) args', tysArgs)
                   
        _ -> fail $ "tcMethodInv: Unsupported method call"

  let (MSig tyR pR psIs psPars pW lExp lMods exns nnps isNative) = msig
  -- Check argument's null type
  let nts = map nullFromStateType tysArgs
  let toCheck = [(p, nt, arg) | nnp <- nnps, (p, Just nt, arg) <- zip3 psIs nts args, nnp == p]
  mapM_ (\(p,nt,arg) -> check (not $ nullable nt) $ toUndef $
                    "When calling method " ++ prettyPrint n ++ ":\n" ++
                    "Parameter: " ++ prettyPrint p ++ " is not allowed to be null while\n" ++
                    "Expression: " ++ prettyPrint arg ++ " can't be assumed such as."
        ) toCheck
  -- Check lockstates
  l <- getCurrentLockState
  check (null (lExp \\ l)) $ toUndef $
            "Lockstate too weak when calling method " ++ prettyPrint n ++ ":\n" ++ 
            "Required lock state: " ++ prettyPrint lExp ++ "\n" ++
            "Current lock state: " ++ prettyPrint l
  -- Check argument constraints
  let !subst = zip psIs psArgs
      !tyR'  = substTypeParPols subst tyR
      (pR':pW':psPars') = map (substParPols subst) (pR:pW:psPars)
      (!exnPs, !_exnAcs) = 
          unzip [ ((t, (rX', wX')),  (ExnType t, (wX', modsX))) |
                  (t, ExnSig rX wX modsX) <- exns,
                  let rX' = substParPols subst rX, 
                  let wX' = substParPols subst wX 
                ]
  mapM_ (\(arg,argP,parP) -> 
                  constraintLS argP parP $ toUndef $
                      "Method applied to argument with too restrictive policy:\n" ++ 
                      "Method invocation: " ++ prettyPrint mi ++ "\n" ++
                      "Argument: " ++ prettyPrint arg ++ "\n" ++
                      "  with policy: " ++ prettyPrint argP ++ "\n" ++
                      "Declared policy bound: " ++ prettyPrint parP
             ) (zip3 args psArgs psPars')
  -- Check E[branchPC](*) <= pW
  bpcs <- getBranchPC_
  constraintPC bpcs pW' $ \p src -> toUndef $
          "Method " ++ prettyPrint n ++ " with declared write effect " ++ prettyPrint pW' ++
          " not allowed in " ++ src ++
          " with write effect bound " ++ prettyPrint p          
  -- Check exnPC(S) <= pW
  epc <- getExnPC
  constraintPC epc pW' $ \p src -> toUndef $
           "Method " ++ prettyPrint n ++ " with declared write effect " ++ prettyPrint pW' ++
           " not allowed in " ++ src ++
           " with write effect bound " ++ prettyPrint p
  -- Check Exns(X)[write] <= E[exns](X)[write] AND
  -- Check Exns(X)[read]  >= E[exns](X)[read]  
  mapM_ (uncurry $ exnConsistent (Left n)) exnPs

  -- Fix outgoing state
--  let exnsT = [ (ExnType tX, (wX, modsX)) | ((tX, (_, wX)), modsX) <- zip exnsPs ]
--      exnsT = map (first ExnType) exnPs
--  activateExns exnAcs    -- ==> S' = Sn[exns{X +-> (Sx, exns(X)[write])}]
  applyLockMods lMods    -- ==> S'' = S'[lockMods ||>>= lMods, 
--  scrambleState          -- ==>          state scrambled]

  styR <- getStateType Nothing Nothing tyR'
  return (styR, pE `join` pR', fmap (setNative isNative) $ ef styR)


--substExnParPols :: [(Ident (), ActorPolicy)] -> ExnSig -> (ActorPolicy, ActorPolicy)
--substExnParPols subst (ExnSig rX wX _ms) = 
--    (substParPrgPols subst rX, substParPrgPols subst wX)

-----------------------------------
{-- Policies

tcPolicy :: Exp () -> TcCodeM ActorPolicy
tcPolicy e = do
  (sty, _, _) <- tcExp e
  case mPolicyPol sty of
    Just (KnownPolicy pol) -> return pol
    Just pb -> panic (tcExpModule ++ ".tcPolicy") $
               "Runtime policy bounds: " ++ show pb
    Nothing -> panic (tcExpModule ++ ".tcPolicy") $
               "Non-policy type for policy: " ++ show e
-}
-----------------------------------
-- Policy expressions
-- Treat them as pure compile-time for now

tcPolicyExp :: PolicyExp SourcePos -> TcCodeM (PrgPolicy TcActor)
tcPolicyExp (PolicyLit _ cs) = do
  tcCs <- mapM tcClause cs
  return (TcPolicy tcCs)
tcPolicyExp pe@(PolicyOf _ i) = do
  (_, _, param) <- lookupVar Nothing i
  check param $
            toUndef $ "policyof may only be used on parameters: " ++ prettyPrint pe
  ct <- isCompileTime
  check ct $
        toUndef $ "policyof may only be used in signatures and policy modifiers: "
                ++ prettyPrint pe
  return $ TcRigidVar True (unIdent i)
tcPolicyExp (PolicyTypeVar _ i) = do
  _ <- lookupVar Nothing i
  return $ TcRigidVar False (unIdent i)
tcPolicyExp (PolicyThis _) = return TcThis
 
tcClause :: Clause SourcePos -> TcCodeM (TcClause TcActor)
tcClause (Clause _ h ats) = do
  tcH <- tcActor h
  tcAs <- mapM tcAtom ats
  return (TcClause tcH tcAs)

tcAtom :: Atom SourcePos -> TcCodeM TcAtom
tcAtom (Atom _ n@(Name _ LName mPre i) as) = do
  LSig _ ar _ <- lookupLock mPre i
  check (length as == ar) $ toUndef $ "Arity mismatch in policy"
  tcAs <- mapM tcActor as
  return (TcAtom n tcAs)
tcAtom (Atom _ n _) = panic (tcExpModule ++ ".tcAtom") $
                      "None-lock name: " ++ show n

tcActor :: Actor SourcePos -> TcCodeM TcActor
tcActor (Var   _ i) = return $ TcVar (unIdent i)
tcActor (Actor _ n) = TcActor <$> tcActorName n

tcActorName :: ActorName SourcePos -> TcCodeM ActorId
tcActorName (ActorName    sp n) = do
  (sty,_,_) <- tcExp $ ExpName sp n
  case mActorId sty of
    Just aid -> return aid
    Nothing  -> panic (tcExpModule ++ ".tcActorName")
                $ "Non-actor type for actor name: " ++ show (n, sty)

tcActorName (ActorTypeVar _ i) = return $ ActorTPVar $ unIdent i

--------------------------------------------------------------------------------
{-- Type-checking types

tcSrcType :: Type SourcePos -> TcCodeM TcType
tcSrcType (PrimType _ pt) = return $ TcPrimT pt
tcSrcType (RefType  _ rt) = TcRefT <$> tcSrcRefType rt
tcSrcType _ = panic (tcExpModule ++ ".tcSrcType")
              "AntiQType should not appear in AST being type-checked"

tcSrcRefType :: RefType SourcePos -> TcCodeM TcRefType
tcSrcRefType (TypeVariable _ i) = return $ TcTypeVar $ unIdent i
tcSrcRefType (ArrayType _ t mps) = do
  ty <- tcSrcType t
  pols <- mapM (maybe (return bottom) tcPolicy) mps
  let (TcRefT arrTy) = mkArrayType ty pols
  return arrTy
tcSrcRefType (ClassRefType _ ct) = TcClsRefT <$> tcSrcClsType ct


tcSrcClsType :: ClassType SourcePos -> TcCodeM TcClassType
tcSrcClsType _ct@(ClassType _ n tas) = do
--  debugPrint $ "Evaluating class type: " ++ show _ct
  baseTm <- liftTcDeclM getTypeMap
  -- debugPrint $ "Current type map: " ++ show baseTm
  (tps,_iaps,_tsig) <- case lookupNamed types n baseTm of
                         Nothing -> liftTcDeclM $ fetchType n 
                                    -- fail $ "Unknown type: " ++ prettyPrint n
                         Just res -> return res

--  debugPrint $ "Type found"
  tArgs <- mapM (uncurry tcSrcTypeArg) (zip tps tas)
--  debugPrint "Type arguments evaluated"
  return $ TcClassT n tArgs

-}
tcSrcType :: Type SourcePos -> TcCodeM (Type T)
tcSrcType (PrimType _ pt) = return $ PrimType Nothing (notAppl pt)
tcSrcType (RefType  _ rt) = RefType Nothing <$> tcSrcRefType rt
tcSrcType _ = panic (tcExpModule ++ ".tcSrcType")
              "AntiQType should not appear in AST being type-checked"


tcSrcRefType :: RefType SourcePos -> TcCodeM (RefType T)
tcSrcRefType (TypeVariable _ i) = return $ TypeVariable Nothing (notAppl i)
tcSrcRefType (ArrayType _ t mps) = do
  t' <- tcSrcType t
  _pols <- mapM (maybe (return bottom) tcPolicy) mps
  return $ ArrayType Nothing t' (map (fmap notAppl) mps)
tcSrcRefType (ClassRefType _ ct) = ClassRefType Nothing <$> tcSrcClsType ct


tcSrcClsType :: ClassType SourcePos -> TcCodeM (ClassType T)
tcSrcClsType (ClassType _ n tas) = do
  baseTm <- liftTcDeclM getTypeMap
  -- debugPrint $ "Current type map: " ++ show baseTm
  (tps,_iaps,_tsig) <- case lookupNamed types n baseTm of
                         Nothing -> liftTcDeclM $ fetchType n 
                                    -- fail $ "Unknown type: " ++ prettyPrint n
                         Just res -> return res
  tArgs <- mapM (uncurry tcSrcTypeArg) (zip tps tas)
  return $ ClassType Nothing (notAppl n) tArgs

tcSrcTypeArg :: TypeParam SourcePos -> TypeArgument SourcePos -> TcCodeM (TypeArgument T)
tcSrcTypeArg tp (ActualArg _ a) = ActualArg Nothing <$> tcSrcNWTypeArg tp a
tcSrcTypeArg _ _ = fail "tcSrcTypeArg: Wildcards not yet supported"

tcSrcNWTypeArg :: TypeParam SourcePos -> NonWildTypeArgument SourcePos -> TcCodeM (NonWildTypeArgument T)
tcSrcNWTypeArg (TypeParam {}) n@(ActualName {}) = return $ notAppl n
  
tcSrcNWTypeArg (TypeParam {}) (ActualType _ rt) = 
    ActualType Nothing <$> tcSrcRefType rt
tcSrcNWTypeArg (ActorParam {}) (ActualName _ n) = 
    return $ ActualName Nothing (fmap (const $ Just (actorT, False)) n)

-- Policies may be names, or special expressions -- TODO: names must be final
tcSrcNWTypeArg (PolicyParam {}) (ActualName _ n) = 
    return $ ActualName Nothing (fmap (const $ Just (policyT, False)) n)

tcSrcNWTypeArg (PolicyParam {}) (ActualExp  _ e) = do
  (_tyE, _polE, e') <- tcExp e
  -- TODO: Also check that tyE is a policy type?
  return $ ActualExp Nothing e'

-- Lock states must be locks
tcSrcNWTypeArg (LockStateParam {}) (ActualLockState _ ls) = 
    return $ ActualLockState Nothing (map notAppl ls)


tcSrcNWTypeArg tp nwta = 
    fail $ "Trying to instantiate type parameter " ++ prettyPrint tp ++
           " with incompatible type argument " ++ prettyPrint nwta

{-

tcSrcTypeArg :: TypeParam SourcePos -> TypeArgument SourcePos -> TcCodeM TcTypeArg
tcSrcTypeArg tp (ActualArg _ a) = tcSrcNWTypeArg tp a
tcSrcTypeArg _ _ = fail "tcSrcTypeArg: Wildcards not yet supported"

tcSrcNWTypeArg :: TypeParam SourcePos -> NonWildTypeArgument SourcePos -> TcCodeM TcTypeArg
-- Types may be names or types -- TODO: Check bounds
tcSrcNWTypeArg (TypeParam {}) (ActualName sp n) = do
    TcActualType . TcClsRefT <$> tcSrcClsType (ClassType sp n [])
tcSrcNWTypeArg (TypeParam {}) (ActualType _ rt) = TcActualType <$> tcSrcRefType rt
-- Actors may only be names -- TODO: must be final
tcSrcNWTypeArg (ActorParam {}) (ActualName sp n) = 
    TcActualActor <$> tcActorName (ActorName sp n)
-- Policies may be names, or special expressions -- TODO: names must be final
tcSrcNWTypeArg (PolicyParam {}) (ActualName sp n) = 
    TcActualPolicy <$> tcPolicy (ExpName sp n)
tcSrcNWTypeArg (PolicyParam {}) (ActualExp  _ e) = 
    TcActualPolicy <$> tcPolicy e
-- Lock states must be locks
tcSrcNWTypeArg (LockStateParam {}) (ActualLockState _ ls) = 
    TcActualLockState <$> mapM tcLock ls

tcSrcNWTypeArg tp nwta = 
    fail $ "Trying to instantiate type parameter " ++ prettyPrint tp ++
           " with incompatible type argument " ++ prettyPrint nwta

-----------------------------------}
-- Policies

tcPolicy :: Exp SourcePos -> TcCodeM ActorPolicy
tcPolicy e = withCompileTimeStatus True $ do
  (sty, _, _) <- tcExp e
  case mPolicyPol sty of
    Just (KnownPolicy pol) -> return pol
    Just pb -> panic (tcExpModule ++ ".tcPolicy") $
               "Runtime policy bounds: " ++ show pb
    Nothing -> panic (tcExpModule ++ ".tcPolicy") $
               "Non-policy type for policy: " ++ show e

tcLock :: Lock SourcePos -> TcCodeM TcLock
tcLock (Lock sp n@(Name spN _nt mPre i) ans) = do
  tm <- case mPre of
          Nothing -> liftTcDeclM getTypeMap
          Just pre -> do
              let preT = ClassType spN pre []
              preTy <- evalSrcClsType genBot preT
              tm <- getTypeMap
              case lookupTypeOfT (clsTypeToType preTy) tm of
                Left Nothing -> panic (tcExpModule ++ ".tcLock")
                                $ "Just evaluated class type " ++ prettyPrint pre ++
                                  " but now it doesn't exist!"
                Left (Just err) -> panic (tcExpModule ++ ".tcLock")
                                   $ err
                Right (_, tsig) -> return $ tMembers tsig

  case Map.lookup (unIdent i) $ locks tm of
    Just lsig -> do
      check (length ans == lArity lsig) $
        mkError (LArityMismatch (prettyPrint n) (lArity lsig) (length ans)) sp
    Nothing -> fail $ "No such lock: " ++ prettyPrint n
  aids <- mapM tcActorName ans
  return $ TcLock n aids
tcLock (LockVar _ i) = return $ TcLockVar $ unIdent i
tcLock l = panic (tcExpModule ++ ".tcLock")
           $ show l
  
-----------------------------------
--    Types of operators         --
-----------------------------------

opType :: Op SourcePos -> TcStateType -> TcStateType -> TcCodeM TcStateType
-- First the special cases: policy operators, and String conversion
opType (Mult _) (TcPolicyPolT p1) (TcPolicyPolT p2) = return (TcPolicyPolT (p1 `join` p2))
opType (Add  _) (TcPolicyPolT p1) (TcPolicyPolT p2) = return (TcPolicyPolT (p1 `meet` p2))
opType (Add  _) t1 t2 | let sT = clsTypeToType stringT,
                        unStateType t1 == sT || unStateType t2 == sT = getStateType Nothing Nothing sT

opType op t1 t2
    -- Numeric operators
    | op `elem` (map ($(defaultPos)) [Mult, Div, Rem, Add, Sub]) = do
        check (isNumConvertible t1) $ toUndef $
              "Numeric operator " ++ prettyPrint op ++ 
                " used with non-numeric operand of type " ++ prettyPrint t1
        check (isNumConvertible t2) $ toUndef $
              "Numeric operator " ++ prettyPrint op ++ 
              " used with non-numeric operand of type " ++ prettyPrint t2
        return $ binaryNumPromote_ t1 t2

    -- Shift operators
    | op `elem` (map ($(defaultPos)) [LShift, RShift, RRShift]) = do
        check (isIntConvertible t1) $ toUndef $
              "Shift operator " ++ prettyPrint op ++
                " used with non-integral operand of type " ++ prettyPrint t1
        check (isIntConvertible t2) $ toUndef $
              "Shift operator " ++ prettyPrint op ++
                " used with non-integral operand of type " ++ prettyPrint t2
        return $ unaryNumPromote_ t1

    -- Relational operators
    | op `elem` (map ($(defaultPos)) [LThan, GThan, LThanE, GThanE]) = do
        check (isNumConvertible t1) $ toUndef $
              "Numerical comparison operator " ++ prettyPrint op ++ 
               " used with non-numeric operand of type " ++ prettyPrint t1
        check (isNumConvertible t2) $ toUndef $
              " Numerical comparison operator " ++ prettyPrint op ++ 
               " used with non-numeric operand of type " ++ prettyPrint t2
        return $ stateType booleanT

    | op `elem` [Equal defaultPos, NotEq defaultPos] = do
        case binaryNumPromote t1 t2 of
          Just _ -> return ()
          _ | isBoolConvertible t1 && isBoolConvertible t2 -> return ()
            | isRefType t1 && isRefType t2 -> return ()
          _ -> failEC () $ toUndef $ "Equality operator " ++ prettyPrint op ++
                       " used with incomparable operands of types " ++
                       prettyPrint t1 ++ " and " ++ prettyPrint t2
        return $ stateType booleanT

    | op `elem` [And defaultPos, Or defaultPos, Xor defaultPos] =
        if isBoolConvertible t1 
         then do
           check (isBoolConvertible t2) $ toUndef $
                     "Logical operator " ++ prettyPrint op ++
                     " used with non-boolean operand of type " ++ prettyPrint t2
           return $ stateType booleanT
         else if isIntConvertible t1
               then do
                 check (isIntConvertible t2) $ toUndef $
                       "Bitwise operator " ++ prettyPrint op ++
                       " used with non-integral operand of type " ++ prettyPrint t2
                 return $ binaryNumPromote_ t1 t2
               else failE $ toUndef $ "Bitwise/logical operator " ++ prettyPrint op ++
                             " used with non-integral and non-boolean operand of type " ++
                             prettyPrint t1
    | op `elem` [CAnd defaultPos, COr defaultPos] = do
        check (isBoolConvertible t1) $ toUndef $
                  "Logical operator " ++ prettyPrint op ++
                   " used with non-boolean operand of type " ++ prettyPrint t1
        check (isBoolConvertible t2) $ toUndef $
                  "Logical operator " ++ prettyPrint op ++
                   " used with non-boolean operand of type " ++ prettyPrint t2
        return $ stateType booleanT

opType op _ _ = panic (tcExpModule ++ ".opType") $ show op
{-
splitName :: Name () -> (Maybe (Name ()), Name ())
splitName (Name _ is) = 
    let (o,f) = (init is, last is)
        mo = if null o then Nothing else Just (Name () o)
    in (mo, Name () [f])
splitName _ = panic (tcExpModule ++ ".splitName")
              "AntiQName should not appear in AST being type-checked"
-}
-}