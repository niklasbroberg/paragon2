{-# LANGUAGE PatternGuards, FlexibleInstances, FlexibleContexts #-}
module Language.Java.Paragon.TypeCheck.Monad
    (
{-     check, checkM, ignore, orElse, maybeM,
     withFold, withFoldMap,

     getReturn,
     extendVarEnvList, extendVarEnv,

     lookupPrefixName,
     lookupVar, lookupActorName,

     --lookupField,
     lookupFieldT,
     lookupMethod, lookupMethodT,
     lookupConstr,
     lookupLock,
     lookupExn, registerExn, registerExns,

     extendLockEnv,

     getBranchPC, getBranchPC_, extendBranchPC,
     addBranchPC, addBranchPCList,

     getActorId, setActorId,
     newActorId, newActorIdWith, newUnknownId,
     freshActorId, unknownActorId,
     scrambleActors,

     getPolicy,

     getExnPC, throwExn,
     activateExns, deactivateExn,
     getExnState, mergeActiveExnStates, useExnState,

     getCurrentPC,

     getCurrentLockState, applyLockMods,
     openLock, closeLock,

     newMetaPolVar,

     constraint, constraintPC, constraintLS,
     exnConsistent,

     extendTypeMapP, extendTypeMapT, -- lookupPkgTypeMap,
--     getTypeMap, withTypeMap,

     evalSrcType, evalSrcRefType, evalSrcClsType,
     evalSrcTypeArg, evalSrcNWTypeArg,
     evalReturnType,

     getReadPolicy, getWritePolicy, getLockPolicy,
     getParamPolicy, getReturnPolicy,

     --fromSrcType,
                       (<:),

     evalPolicy, evalPolicyExp,
     evalLock, evalActor,
-}
     module Language.Java.Paragon.TypeCheck.Monad.TcCodeM,
     module Language.Java.Paragon.TypeCheck.Monad,

{-     debug, debugTc,

     solve
-}
    ) where

import Language.Java.Paragon.Error
import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.TypeCheck.Monad.TcDeclM
import Language.Java.Paragon.TypeCheck.Monad.TcCodeM

import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.TypeMap

import Language.Java.Paragon.PolicyLang

import Language.Java.Paragon.TypeCheck.NullAnalysis

import Control.Monad hiding (join)
import Control.Applicative ( (<$>), (<*>) )
import qualified Data.Map as Map
import Data.List (intersperse)
import Data.Maybe (isJust)
import Data.Generics.Uniplate.Data

import qualified Data.ByteString.Char8 as B

--debug :: String -> TcDeclM ()
--debug str = liftIO $ finePrint $ "DEBUG: " ++ str

--debugTc :: String -> TcCodeM ()
--debugTc = liftTcDeclM . debug

-- TODO BART fail -> failE

monadModule :: String
monadModule = typeCheckerBase ++ ".Monad"

--------------------------------------------
--          Working with the env          --
--------------------------------------------

-- this

--getThisType :: TcCodeM TcType
--getThisType = liftCont getThisT

-- returns

getReturn :: TcCodeM (TcType, ActorPolicy)
getReturn = do
  mRet <- returnI <$> getEnv
  case mRet of
    Nothing -> fail "Attempting to use 'return' in a simple expression context"
    Just ret -> return ret

{-
registerReturn :: TcType -> TcPolicy -> TcCodeM r a -> TcCodeM r a
registerReturn ty p = withEnv $ \env -> env { returnI = (ty,p) }
-}
-- lookup entities

--fieldEnvToVars :: TcCodeM r a -> TcCodeM r a
--fieldEnvToVars = withEnv $ \env -> env { vars = fields (typemap env) }


extendVarEnvList :: [(B.ByteString, VarFieldSig)] -> TcCodeM a -> TcCodeM a
extendVarEnvList vs = withEnv $ \env ->
  let (oldVmap:oldVmaps) = vars env
      newVmap = foldl (\m (i,vti) -> Map.insert i vti m) oldVmap vs
  in return $ env { vars = newVmap : oldVmaps }

extendVarEnv :: B.ByteString -> VarFieldSig -> TcCodeM a -> TcCodeM a
--extendVarEnv i = extendVarEnvN i
--extendVarEnvN :: Ident -> VarFieldSig -> TcCodeM a -> TcCodeM a
extendVarEnv i vti = withEnv $ \env -> do
  let (oldVmap:oldVmaps) = vars env
  if Map.notMember i oldVmap
    then return $ env { vars = Map.insert i vti oldVmap : oldVmaps }
    else failE $ mkErrorFromInfo $ VariableAlreadyDefined (B.unpack i)

lookupActorName :: ActorName SourcePos -> TcCodeM (TcStateType, ActorPolicy)
lookupActorName (ActorName _ nam@(Name _ nt mPre i))
    | nt == EName =
        do (ty, pol, _, _) <- lookupVar mPre i
           return (ty, pol)
    | otherwise   = panic (monadModule ++ ".lookupActorName")
                                 $ "Not an EName: " ++ show nam
lookupActorName (ActorTypeVar _ _rt i) = do
  (ty, pol, _, _) <- lookupVar Nothing i
  return (ty, pol)

lookupActorName n = panic (monadModule ++ ".lookupActorName")
                    $ "Unexpected AntiQName: " ++ show n

type Sig = ([TypeParam SourcePos], [B.ByteString], [TcType], Bool)
type APPairs = [(ActorPolicy, ActorPolicy)]

instance Pretty Sig where
  pretty (tps, _, tys, isva) = pretty (tps, tys, isva)


findBestMethod
    :: [TypeArgument SourcePos]
    -> [TcType]
    -> [ActorPolicy]
    -> [Sig]  -- Works for both methods and constrs
    -> TcCodeM [(Sig, APPairs)]
findBestMethod tArgs argTys argPs candidates = do
  --debugPrint $ "findBestMethod: "
  --debugPrint $ "  Candidates: "
  --mapM_ (debugPrint . ("    " ++) . prettyPrint) candidates
  --debugPrint $ "  Argument types: "
  --debugPrint $ "    " ++ prettyPrint argTys
  mps <- mapM isApplicable candidates
  res <- findBestFit [ (c, ps) | (c, Just ps) <- zip candidates mps ]
  --debugPrint $ "Best method done"
  return res
  -- findBestFit =<< filterM isApplicable candidates

  where isApplicable :: Sig -> TcCodeM (Maybe APPairs)
        isApplicable (tps, pIs, pTys, isVA) = do
          b1 <- checkArgs tps tArgs
          if b1 then do
                  tyArgs <- zipWithM (evalSrcTypeArg genBot) tps tArgs
                  let subst = zip pIs argPs
                  pTys' <- mapM (substTypeParPols subst) $
                                instantiate (zip tps tyArgs) pTys
                  --debugPrint $ "isApplicable: "
                  --               ++ show (isVA, map prettyPrint pTys', map prettyPrint argTys)
                  ps <- checkTys isVA pTys' argTys
                  --debugPrint $ "     .... "
                  --               ++ maybe "Nope" (prettyPrint . (map (\(a,b) -> [a,b]))) ps
                  return ps
           else return Nothing

        checkArgs :: [TypeParam SourcePos] -> [TypeArgument SourcePos] -> TcCodeM Bool
        checkArgs [] [] = return True
        checkArgs (tp:tps) (ta:tas) = (&&) <$> checkArg tp ta <*> checkArgs tps tas
        checkArgs _ _ = return False

        -- this needs to be done in TcCodeM, to account for local variables.
        checkArg :: TypeParam SourcePos -> TypeArgument SourcePos -> TcCodeM Bool
        checkArg tp ta = isRight <$> tryM (evalSrcTypeArg genBot tp ta)

        checkTys :: Bool -> [TcType] -> [TcType] -> TcCodeM (Maybe APPairs)
        checkTys _ [] [] = return $ Just []
        checkTys b ps as
            | not b && length ps /= length as = return Nothing
            | b && length ps > length as + 1  = return Nothing
        checkTys True [p] [a] = do
          mps <- a `isAssignableTo` p
          case mps of
            Just _ -> return mps
            Nothing -> bottomM >>= \bt -> a `isAssignableTo` arrayType p bt
        checkTys True [p] as = do
          mpps <- zipWithM isAssignableTo as (repeat p) -- [M [(P,P)]]
          return $ concat <$> sequence mpps

        checkTys b (p:ps) (a:as) = do
          mps <- a `isAssignableTo` p
          case mps of
            Just aps -> do mAps' <- checkTys b ps as
                           return $ fmap (aps++) mAps'
            Nothing -> return Nothing
        checkTys _ _ _ = return Nothing

        findBestFit :: [(Sig, APPairs)] -> TcCodeM [(Sig, APPairs)]
        findBestFit [] = return []
        findBestFit (x:xs) = go [x] xs

        go :: [(Sig, APPairs)] -> [(Sig, APPairs)] -> TcCodeM [(Sig, APPairs)]
        go xs [] = return xs
        go xs (y:ys) = do
          bs0 <- mapM (\x -> fst y `moreSpecificThan` fst x) xs
          if and bs0 then go [y] ys
           else do bs1 <- mapM (\x -> fst x `moreSpecificThan` fst y) xs
                   if and bs1 then go xs ys else go (y:xs) ys

        moreSpecificThan :: Sig -> Sig -> TcCodeM Bool
        moreSpecificThan (_,_,ps1,False) (_,_,ps2,False) = do
                                           mpss <- zipWithM isAssignableTo ps1 ps2 -- [M [(P,P)]]
                                           return $ isJust $ sequence mpss
        moreSpecificThan _ _ = fail "Varargs not yet supported"
{-        moreSpecificThan (_,ps1,True ) (_,ps2,True ) = do
          let n = length ps1
              k = length ps2
          undefined n k
        moreSpecificThan _ _ = undefined -}

        isRight :: Either a b -> Bool
        isRight (Right _) = True
        isRight _ = False

-- | Lookup the signature of a method, and the policy of its access path.
lookupMethod :: Maybe (Name SourcePos)    -- Access path
             -> Ident SourcePos           -- Method name
             -> [TypeArgument SourcePos]  -- Type arguments
             -> [TcType]           -- Argument types
             -> [ActorPolicy]      -- Argument policies
             -> TcCodeM (ActorPolicy, [TypeParam SourcePos], MethodSig)
lookupMethod mPre i tArgs argTys argPs = do
  --debugPrint $ "lookupMethod: " ++ show (mPre, i, argTys)
  baseTm <- getTypeMap
  (mPreTy, preTm, prePol, _) <-
    case mPre of
      Nothing -> bottomM >>= \bt ->
                  return (Nothing, baseTm, bt, Nothing)
      Just pre -> lookupPrefixName pre
  case Map.lookup (unIdent i) $ methods preTm of
    Nothing -> fail $ case mPreTy of
                       Just preTy ->
                           "Type " ++ prettyPrint preTy ++
                                   " does not have a method named " ++ prettyPrint i
                       Nothing -> "No method named " ++ prettyPrint i ++
                                    " is in scope"
    Just methodMap -> do
      --debugPrint $ prettyPrint methodMap
      bests <- findBestMethod tArgs argTys argPs (getSigs methodMap)
      case bests of
        [] -> fail $ case mPreTy of
                       Just preTy ->
                           "Type " ++ prettyPrint preTy ++
                             " does not have a method named " ++ prettyPrint i ++
                             " matching argument types (" ++
                             unwords (intersperse ", " $ map prettyPrint argTys) ++
                             ")"
                       Nothing -> "No method named " ++ prettyPrint i ++
                                  " matching argument types (" ++
                                 unwords (intersperse ", " $ map prettyPrint argTys) ++
                                 ") is in scope"

        (_:_:_) -> fail $ case mPreTy of
                            Just preTy ->
                                "Type " ++ prettyPrint preTy ++
                                  " has more than one most specific method " ++ prettyPrint i ++
                                  " matching argument types (" ++
                                  unwords (intersperse ", " $ map prettyPrint argTys) ++
                                  ")"
                            Nothing -> "More than one most specific method named " ++ prettyPrint i ++
                                       " matching argument types (" ++
                                      unwords (intersperse ", " $ map prettyPrint argTys) ++
                                      ") is in scope"

        [((tps,_,ts,isVA), aps)] ->
            let sig = (tps,ts,isVA) in
             case Map.lookup sig methodMap of
              Nothing -> panic (monadModule ++ ".lookupMethod")
                         $ "Sig must be one of the keys of methodMap: " ++ show sig
              Just msig -> do
                        mapM_ (\(p,q) -> do
                                 constraint emptyLockSet p q $ toUndef $
                                    "Cannot unify policy type parameters at call to method " ++ prettyPrint i ++ ":\n" ++
                                    "  p: " ++ prettyPrint p ++ "\n" ++
                                    "  q: " ++ prettyPrint q
                                 constraint emptyLockSet q p $ toUndef $
                                    "Cannot unify policy type parameters at call to method " ++ prettyPrint i ++ ":\n" ++
                                    "  p: " ++ prettyPrint q ++ "\n" ++
                                    "  q: " ++ prettyPrint p) aps
                        return (prePol, tps, msig)


-- | Lookup the signature of a lock -- note that all locks are static,
--   so the policy of the access path is irrelevant.
lookupLock :: Maybe (Name SourcePos) -- Access path
           -> Ident SourcePos        -- Name of lock
           -> TcCodeM LockSig
lookupLock mPre i@(Ident sp _) = do
  baseTm <- getTypeMap
  preTm <- case mPre of
             Nothing -> return baseTm
             Just pre -> do
                       (_, preTm, _, _) <- lookupPrefixName pre
                       return preTm
  case Map.lookup (unIdent i) $ locks preTm of
    Just lsig -> return lsig
    Nothing -> do
      fail $ "Lock " ++ prettyPrint (Name sp LName mPre i) ++ " not in scope"

lookupFieldT :: TcStateType -> Ident SourcePos -> TcCodeM VarFieldSig
lookupFieldT typ i = do
  check (isRefType typ) $ toUndef ("Not a reference type: " ++ prettyPrint typ)
  aSig <- lookupTypeOfStateType typ
  case Map.lookup (unIdent i) (fields $ tMembers aSig) of
    Just vti -> return vti
    Nothing -> failE $ toUndef $ "Class " ++ prettyPrint typ
                      ++ " does not have a field named " ++ prettyPrint i

lookupMethodT :: TcStateType
              -> Ident SourcePos
              -> [TypeArgument SourcePos]
              -> [TcType]
              -> [ActorPolicy]
              -> TcCodeM ([TypeParam SourcePos], MethodSig)
lookupMethodT typ i tArgs argTys argPs = do
  check (isRefType typ) $ toUndef $ "Not a reference type: " ++ prettyPrint typ
  aSig <- lookupTypeOfStateType typ
  case Map.lookup (unIdent i) (methods $ tMembers aSig) of
    Nothing -> fail $ "Class " ++ prettyPrint typ
                      ++ " does not have a method named " ++ prettyPrint i
    Just mMap -> do
      bests <- findBestMethod tArgs argTys argPs (getSigs mMap)
      case bests of
        [] -> fail $
                "Type " ++ prettyPrint typ ++
                            " does not have a method named " ++ prettyPrint i ++
                            " matching argument types (" ++
                            unwords (intersperse ", " $ map prettyPrint argTys) ++
                            ")"

        (_:_:_) -> fail $
                     "Type " ++ prettyPrint typ ++
                                 " has more than one most specific method " ++ prettyPrint i ++
                                 " matching argument types (" ++
                                 unwords (intersperse ", " $ map prettyPrint argTys) ++
                                 ")"

        [((tps,_,ts,isVA), aps)] ->
            let sig = (tps,ts,isVA) in
             case Map.lookup sig mMap of
              Nothing -> panic (monadModule ++ ".lookupMethodT")
                         $ "Sig must be one of the keys of methodMap: " ++ show sig
              Just msig -> do
                        mapM_ (\(p,q) -> do
                                 constraint emptyLockSet p q $ toUndef $
                                    "Cannot unify policy type parameters at method call:\n" ++
                                    "  p: " ++ prettyPrint p ++ "\n" ++
                                    "  q: " ++ prettyPrint q
                                 constraint emptyLockSet q p $ toUndef $
                                    "Cannot unify policy type parameters at method call:\n" ++
                                    "  p: " ++ prettyPrint q ++ "\n" ++
                                    "  q: " ++ prettyPrint p) aps
                        return (tps, msig)

lookupConstr :: TcClassType
             -> [TypeArgument SourcePos]
             -> ActorPolicy -- policyof(this), i.e. the result
             -> [TcType]
             -> [ActorPolicy]
             -> TcCodeM ([TypeParam SourcePos], [(RefType SourcePos, B.ByteString)], ConstrSig)
lookupConstr ctyp tArgs pThis argTys argPs = do
  --debugPrint $ "\n\n######## Looking up constructor! ######## \n"
  let typ = clsTypeToType ctyp
  --debugPrint $ "typ: " ++ prettyPrint typ
--  tm <- getTypeMap
--  debugPrint $ prettyPrint tm
  (iaps, aSig) <- lookupTypeOfType typ
--  debugPrint $ "aSig: " ++ show aSig
  let cMap = constrs $ tMembers aSig
  --debugPrint $ "cMap: "
  --debugPrint $ prettyPrint cMap
  cMap' <- instThis pThis cMap
  bests <- findBestMethod tArgs argTys argPs (getSigsC cMap')
  case bests of
    [] -> fail $ "Type " ++ prettyPrint ctyp ++
                 " does not have a constructor \
                  \matching argument types (" ++
                 unwords (intersperse ", " $ map prettyPrint argTys) ++
                 ")"
    (_:_:_) ->
        fail $ "Type " ++ prettyPrint ctyp ++
                 " has more than one most specific \
                  \constructor matching argument types (" ++
                 unwords (intersperse ", " $ map prettyPrint argTys) ++
                 ")"
    [((tps,_,ts,isVA), aps)] ->
        let sig = (tps, ts, isVA) in
         case Map.lookup sig cMap' of
              Nothing -> panic (monadModule ++ ".lookupConstr")
                         $ "Sig must be one of the keys of constrMap: " ++ show sig
              Just csig -> do
                        mapM_ (\(p,q) -> do
                                 constraint emptyLockSet p q $ toUndef $
                                    "Cannot unify policy type parameters at constructor call:\n" ++
                                    "  p: " ++ prettyPrint p ++ "\n" ++
                                    "  q: " ++ prettyPrint q
                                 constraint emptyLockSet q p $ toUndef $
                                    "Cannot unify policy type parameters at constructor call:\n" ++
                                    "  p: " ++ prettyPrint q ++ "\n" ++
                                    "  q: " ++ prettyPrint p) aps
                        return (tps, iaps, csig)


getSigs :: MethodMap -> [Sig]
getSigs = map getSig . Map.assocs
    where getSig ((tps, pTs, vAr), msig) = (tps, mPars msig, pTs, vAr)

getSigsC :: ConstrMap -> [Sig]
getSigsC = map getSig . Map.assocs
    where getSig ((tps, pTs, vAr), csig) = (tps, cPars csig, pTs, vAr)


substParPols :: Lattice m ActorPolicy =>
                [(B.ByteString, ActorPolicy)] -> ActorPolicy -> m ActorPolicy
substParPols subst (VarPolicy pol) = substParPrgPols subst pol
substParPols subst (MetaJoin p q) = do
  pp <- substParPols subst p
  qq <- substParPols subst q
  pp `lub` qq
substParPols subst (MetaMeet p q) = do
  pp <- substParPols subst p
  qq <- substParPols subst q
  pp `glb` qq
substParPols _ p = return p

substParPrgPols :: Lattice m ActorPolicy =>
                   [(B.ByteString, ActorPolicy)] -> PrgPolicy -> m ActorPolicy
substParPrgPols subst p@(PolicyVar (PolicyOfVar i)) =
    case lookup i subst of
      Just newP -> return newP
      Nothing -> return $ VarPolicy p
substParPrgPols subst (Join p q) = do
  pp <- substParPrgPols subst p
  qq <- substParPrgPols subst q
  pp `lub` qq
substParPrgPols subst (Meet p q) = do
  pp <- substParPrgPols subst p
  qq <- substParPrgPols subst q
  pp `glb` qq
substParPrgPols _ p = return $ VarPolicy p

substTypeParPols :: (HasSubTyping m, Lattice m ActorPolicy) =>
                    [(B.ByteString, ActorPolicy)] -> TcType -> m TcType
substTypeParPols subst (TcRefT rty) = TcRefT <$> substRefTypePPs rty
  where substRefTypePPs rt =
            case rt of
              TcArrayT ty p ->
                  TcArrayT <$> substTypeParPols subst ty <*> substParPols subst p
              TcClsRefT ct  ->
                  TcClsRefT <$> substClsTypePPs ct
              _ -> return rt

        substClsTypePPs (TcClassT n targs) = TcClassT n <$> mapM substTAPPs targs

        substTAPPs (TcActualType rt) = TcActualType <$> substRefTypePPs rt
        substTAPPs (TcActualPolicy p) = TcActualPolicy <$> substParPols subst p
        substTAPPs a = return a

substTypeParPols _ ty = return ty





{-
registerStateType i tyV mSty | tyV == actorT = do
  case mSty of
    Nothing -> actorIdT <$> newActorId i -- fresh generation
    Just sty -> case mActorId sty of
                  Nothing -> panic (monadModule ++ ".registerStateType")
                             $ "Actor state but non-actor target type: "
                                  ++ show (tyV, sty)
                  Just aid -> do
                    newActorIdWith i aid
                    return $ actorIdT aid

registerStateType i tyV mSty | tyV == policyT = do
  let pbs = case mSty of
              Nothing -> PolicyBounds bottom top
              Just sty -> case mPolicyPol sty of
                            Nothing -> panic (monadModule ++ ".registerStateType")
                                       $ "Policy state but non-policy target type: "
                                             ++ show (tyV, sty)
                            Just bs -> bs
  updateState $ \s ->
      s { policySt = Map.insert (mkSimpleName EName i) pbs $ policySt s }
  return $ policyPolT pbs

registerStateType i tyV mSty | Just ct <- mClassType tyV = do
    debugPrint $ "registerStateType: " ++ show (i, tyV, mSty)
    case mSty of
      -- no initialiser
      Nothing -> return $ instanceT ct [] -- ??
      Just sty -> case mInstanceType sty of
                    Just (_, aids) -> do
                      updateState $ \s ->
                          s { instanceSt = Map.insert (mkSimpleName EName i) aids
                                           $ instanceSt s }
                      return $ instanceT ct aids
                    Nothing | isNullType sty -> return $ instanceT ct []
                            | otherwise -> panic (monadModule ++ ".registerStateType")
                               $ "Instance state but non-instance target type: "
                                         ++ show (tyV, sty)



registerStateType _i tyV _mSty = return $ stateType tyV
-}
{-
updateStateType mN _mTyO tyV sty | tyV == actorT = do
  case mActorId sty of
    Just aid -> do
--      maybeM mTyO $ \tyO -> scrambleActors (Just tyO)
      maybeM mN $ \n -> setActorId n aid
      return sty
    _ -> panic (monadModule ++ ".updateStateType")
         $ "Actor state but non-actor target type: "
               ++ show (tyV, sty)

-- TODO
{-
updateStateType mN mTyO tyV mSty | tyV == policyT = do
  case mSty of
    Just sty | Just pbs <- mPolicyPol sty -> do
-}
updateStateType _mN _mTyO ty _sty | isPrimType (stateType ty) = return $ stateType ty
updateStateType mN _mTyO ty sty
    | Just ct <- mClassType ty =
        case sty of
          TcInstance _ aids -> return $ TcInstance ct aids
          _ | isNullType sty -> TcInstance ct <$> getInstanceActors mN ct
          _ | isArrayType sty -> return $ TcInstance ct []
          _ -> panic (monadModule ++ ".updateStateType")
                        $ "Class type target but no instance type"
                          ++ show (ty, sty)

updateStateType _mN _mTyO _ty sty = return sty -- BOGUS!!!


-- Instance Analysis

getInstanceActors :: Maybe (Name SourcePos) -> TcClassType -> TcCodeM [ActorId]
getInstanceActors mn ct@(TcClassT tyN _) = do
  instanceMap <- instanceSt <$> getState
  case maybe Nothing (\n -> Map.lookup n instanceMap) mn of
    Nothing  -> do
      (iaps, _) <- lookupTypeOfType (clsTypeToType ct)
      mapM (instanceActorId . Name defaultPos EName (Just tyN)) iaps
    Just aids -> return aids

-- Policy Analysis

getPolicyBounds :: Maybe (Name SourcePos) -> Maybe TcStateType -> TcCodeM ActorPolicyBounds
getPolicyBounds mn mtyO = do
  policyMap <- policySt <$> getState
  case maybe Nothing (\n -> Map.lookup n policyMap) mn of
    Nothing -> case (mtyO, mn) of
                 (Just styO, Just (Name _ _ _ i)) -> do
                           tsig <- lookupTypeOfStateType styO
                           case Map.lookup i $ policies $ tMembers tsig of
                             Just pol -> return $ KnownPolicy $ RealPolicy pol
                             Nothing  -> return $ PolicyBounds bottom top
                 _ -> return $ PolicyBounds bottom top
    Just pif -> return pif

-- Actor Analysis

getActorId :: Maybe (Name SourcePos) -> Maybe TcStateType -> TcCodeM ActorId
getActorId mn mtyO = do
  actorMap <- actorSt <$> getState
  case maybe Nothing (\n -> Map.lookup n actorMap) mn of
    Nothing -> case (mtyO, mn) of
                 (Just styO, Just (Name _ _ _ i)) -> do
                           tsig <- lookupTypeOfStateType styO
                           case Map.lookup i $ actors $ tMembers tsig of
                             Just aid -> return aid
                             Nothing  -> liftTcDeclM $ unknownActorId
                 _ -> liftTcDeclM $ unknownActorId
    Just ai -> return $ aID ai

setActorId :: Name SourcePos -> ActorId -> TcCodeM ()
setActorId n aid = updateState setAct
  where setAct :: CodeState -> CodeState
        setAct s@(CodeState { actorSt = actMap }) = s { actorSt = Map.adjust replId n actMap }
        replId (AI _ st) = AI aid st


newActorIdWith :: Ident SourcePos -> ActorId -> TcCodeM ()
newActorIdWith i aid = do
  updateState insertAct
      where insertAct :: CodeState -> CodeState
            insertAct s@(CodeState { actorSt = actMap }) =
                s { actorSt = Map.insert (mkSimpleName EName i) (AI aid Stable) actMap }

newActorId :: Ident SourcePos -> TcCodeM ActorId
newActorId i = do
  aid <- liftTcDeclM $ freshActorId (prettyPrint i)
  newActorIdWith i aid
  return aid

newUnknownId :: Ident SourcePos -> TcCodeM ActorId
newUnknownId i = do
  aid <- liftTcDeclM unknownActorId
  newActorIdWith i aid
  return aid
-}

{-
scrambleActors :: Maybe TcType -> TcCodeM ()
scrambleActors mtc = do
  let stb = maybe FullV (FieldV . Just . typeName_) mtc
  state <- getState
  u <- getUniqRef
  newState <- liftIO $ scramble u stb state
  setState newState
-}
-- Exception tracking

-- Lockstate tracking

-- Policy inference


--newRigidPolVar :: TcCodeM TcPolicy
--newRigidPolVar = do
--  uniq <- lift . getUniq =<< getUniqRef
--  return $ TcRigidVar uniq


-- Subtyping/conversion/promotion

-- Note that we do NOT allow unchecked conversion or capture conversion.
-- We don't give crap about backwards compatibility here, and even if we
-- did, we would have to rule it out because it would be unsound.

isAssignableTo :: TcType -> TcType -> TcCodeM (Maybe [(ActorPolicy, ActorPolicy)])
isAssignableTo t1 t2 = do
  case t1 `equivTo` t2 of -- identity conversion
    Just ps -> return $ Just ps
    Nothing -> do
      b <- liftTcDeclM $ t1 `widensTo` t2 -- widening conversion
      return $ if b then Just [] else Nothing

(=<:) :: TcType -> TcStateType -> TcCodeM (Maybe [(ActorPolicy, ActorPolicy)])
lhs =<: rhs = isAssignableTo (unStateType rhs) lhs

equivTo :: TcType -> TcType -> Maybe [(ActorPolicy, ActorPolicy)]
equivTo (TcRefT rt1) (TcRefT rt2) = equivRefT rt1 rt2
  where equivRefT :: TcRefType -> TcRefType -> Maybe [(ActorPolicy, ActorPolicy)]
        equivRefT (TcArrayT t1 p1) (TcArrayT t2 p2) = do
          ps <- t1 `equivTo` t2
          return $ (p1,p2):ps
        equivRefT (TcClsRefT ct1) (TcClsRefT ct2) = equivClsT ct1 ct2
        equivRefT _ _ = if rt1 == rt2 then return [] else Nothing

        equivClsT :: TcClassType -> TcClassType -> Maybe [(ActorPolicy, ActorPolicy)]
        equivClsT (TcClassT n1 tas1) (TcClassT n2 tas2) =
            if n1 /= n2 then Nothing
             else equivTypeArgs tas1 tas2

        equivTypeArgs :: [TcTypeArg] -> [TcTypeArg] -> Maybe [(ActorPolicy, ActorPolicy)]
        equivTypeArgs tas1 tas2 = concat <$> zipWithM equivTypeArg tas1 tas2

        equivTypeArg :: TcTypeArg -> TcTypeArg -> Maybe [(ActorPolicy, ActorPolicy)]
        equivTypeArg (TcActualPolicy p1) (TcActualPolicy p2) = Just [(p1, p2)]
        equivTypeArg (TcActualType r1) (TcActualType r2) = equivRefT r1 r2
        equivTypeArg a1 a2 = if a1 == a2 then return [] else Nothing

equivTo t1 t2 = if t1 == t2 then return [] else Nothing

isCastableTo :: TcType
             -> TcType
             -> TcCodeM (Maybe [(ActorPolicy, ActorPolicy)], Bool) -- (Can be cast, needs reference narrowing)
isCastableTo t1 t2 = do
  -- 'isAssignableTo' handles the cases of identity, primitive widening,
  -- boxing + reference widening and unboxing + primitive widening.
  -- It also handles reference widening, but not with subsequent unboxing.
  mps <- isAssignableTo t1 t2
  case mps of
    Just ps -> return (Just ps, False)
    Nothing -> liftTcDeclM $ do
     -- What we have left is primitive narrowing, primitive widening+narrowing,
     -- reference widening + unboxing, and reference narrowing + optional unboxing.
     -- Only the last one, that includes reference narrowing, can throw a ClassCastException.
     case (t1, t2) of
       (TcPrimT pt1, TcPrimT pt2) -> -- primitive (widening +) narrowing
           return (if pt2 `elem` narrowConvert pt1 ++ widenNarrowConvert pt1 then Just [] else Nothing, False)
       (TcRefT  rt1, TcPrimT pt2)
           | Just ct2 <- box pt2 -> do -- reference widening + unboxing AND
                                       -- reference narrowing + unboxing
               -- We cheat and compare to the boxing of the target instead
               -- since box/unbox are inverses.
               let rt2 = TcClsRefT ct2
               bWide <- rt1 `subTypeOf` rt2
               if bWide then return (Just [], False)
                else return (Just [], True)
       (TcRefT _rt1, TcRefT _rt2) -> do -- reference narrowing, no unboxing
                     -- TODO: There are restrictions here, but not relevant at this point
                     return (Just [], True)
       _ -> return (Nothing, False)

(<<:) :: TcType -> TcStateType -> TcCodeM (Maybe [(ActorPolicy, ActorPolicy)], Bool)
lhs <<: rhs = isCastableTo (unStateType rhs) lhs


-- widening conversion can come in four basic shapes:
-- 1) pt/pt -> widening primitive conversion
-- 2) rt/rt -> widening reference conversion
-- 3) pt/rt -> boxing conversion + widening reference conversion
-- 4) rt/pt -> unboxing conversion + widening primitive conversion
widensTo :: TcType -> TcType -> TcDeclM Bool
widensTo (TcPrimT pt1) (TcPrimT pt2) = return $ pt2 `elem` widenConvert pt1
widensTo (TcRefT   rt1) (TcRefT   rt2) = rt1 `subTypeOf` rt2
widensTo (TcPrimT pt1) t2@(TcRefT _) =
    maybe (return False)
              (\ct -> clsTypeToType ct `widensTo` t2) (box pt1)
widensTo (TcRefT   rt1) t2@(TcPrimT _) =
    case rt1 of
      TcClsRefT ct -> maybe (return False)
                        (\pt -> TcPrimT pt `widensTo` t2) (unbox ct)
      _ -> return False
{-- 5) Paragon-specific types
widensTo t1 t2 | isPolicyType t1 && t2 == policyT  = return True
               | isLockType   t1 && t2 == booleanT = return True
               | isActorType  t1 && t2 == actorT   = return True
-}
widensTo _ _ = return False
{-
instance HasSubTyping TcDeclM where
 --subTypeOf :: TcRefType -> TcRefType -> TcDeclM Bool
 subTypeOf TcNullT _ = return True
 subTypeOf rt1 rt2 = (rt2 `elem`) <$> ([TcClsRefT objectT] ++) <$> superTypes rt1
  where superTypes ::  TcRefType -> TcDeclM [TcRefType]
        superTypes rt = do
          tm <- getTypeMap
          tsig <- case lookupTypeOfRefT rt tm of
                    Left Nothing -> do
                          case rt of
                            TcClsRefT (TcClassT n tas) -> do
                               (tps, _iaps, tsig) <- fetchType n
                               return $ instantiate (zip tps tas) tsig
                            _ -> panic (monadModule ++ ".subTypeOf")
                                 $ show rt

                    Left err -> panic (monadModule ++ ".subTypeOf")
                                $ "Looking up type:" ++ show rt ++ "\nError: " ++ show err
                    Right (_,tsig) -> return tsig
          let sups  = tSupers tsig
              impls = tImpls tsig
              allS  = map TcClsRefT $ sups ++ impls
          supsups <- mapM superTypes allS
          return $ concat $ allS:supsups
-}

------------------------------------------
--        Constraints resolution        --
------------------------------------------

-- Resolution thanks to the transitive closure.
solveConstraints :: [ConstraintWMsg] -> TcDeclM ()
solveConstraints cs = do
      finePrint "Solving constraints..."
      debugPrint $ show (length cs)
      let wcs     = [c | (c, _) <- cs] -- TODO: Take error texts into account
      b <- solve wcs
      check b (toUndef "The system failed to infer the set of unspecified policies ")
      finePrint "Constraints successfully solved!"

{-

checkCstr :: String -> Constraint -> TcDeclM ()
checkCstr str (LRT bs g ls p q) = do
  case lrt bs g ls p q of
    Left b  -> do
      -- add xml node to tree
      check b $ toUndef $ str
    Right _ -> panic (monadModule ++ ".checkCstr")
               $ "This set of constraint should be solved !"
-}

{-
solve :: [ConstraintWMsg] -> TcDeclM ()
solve cs =
    liftIO $ do
      wcs <- return [(p, q) | (LRT _ p q, _) <- cs]
      cvars <- filterM isCstrVar wcs
      cvarsm <- return (foldl linker Map.empty cvars)
      csubsts <- return (Map.foldlWithKey (\cs' x pxs -> foldl (\cs'' px-> (substitution x px cs'')) cs' pxs) wcs cvarsm)
      tobechecked <- filterM (\c -> do b <- (isCstrVar c); return $ not b) csubsts
      mapM_ print tobechecked
      mapM_ (checkCstr "The unspecified variable's policies inference leads, without taking into account the global policy, to an unsolvable system. Please explicite them.") tobechecked

-}


--------------------------------------------------
-- State scrambling

-- 'scramble' should be called at method calls,
-- and will remove everything that is not known
-- not to be affected by that call.
scrambleState :: TcCodeM ()
scrambleState = do
--  s1 <- getState
--  debugPrint $ "\nScrambling: " ++ show s1
  updateState scramble
--  s2 <- getState
--  debugPrint $ "Scrambling done: " ++ show s2 ++ "\n"

scramble :: CodeState -> CodeState
scramble = transformBi scr
    where scr :: VarMap -> VarMap
          scr (VarMap {-aMap-} pMap iMap tMap) =
              VarMap
                -- (deleteIf (const $ not . aStable) aMap)
                (deleteIf (const $ not . pStable) pMap)
                (deleteIf (const $ not . iStable) iMap)
                tMap -- fixed recursively by transformBi

-- 'scrambleT' should be called when a field is
-- updated, and will remove everything that could
-- be an update-through-alias of that field.
scrambleT :: TcRefType -> Ident SourcePos -> Bool -> TcCodeM ()
scrambleT rtyO iF fresh = setState =<< transformBiM scr =<< getState -- "updateStateM"
  where scr :: InstanceInfo -> TcCodeM InstanceInfo
        scr isig = do
             appl <- liftTcDeclM $ iType isig `subTypeOf` rtyO
             return $ if appl && not (fresh && iFresh isig)
                       then isig { iMembers = scrVM $ iMembers isig }
                       else isig

        scrVM :: VarMap -> VarMap
        scrVM (VarMap {-aMap-} pMap iMap tMap) =
            let matches k _v = k == unIdent iF
            in VarMap
                   -- (deleteIf matches aMap)
                   (deleteIf matches pMap)
                   (deleteIf matches iMap)
                   tMap -- will be empty

deleteIf :: Ord k => (k -> v -> Bool) -> Map k v -> Map k v
deleteIf test = snd . Map.partitionWithKey test


varUpdatedNN :: Name SourcePos -> Maybe (Name SourcePos) -> Ident SourcePos -> TcCodeM ()
varUpdatedNN n mPre i = do
  (ty, _, _, _) <- lookupVar mPre i
  _ <- updateStateType (Just (n, True)) (unStateType ty) (Just $ setNullInStateType ty (NotNull, Committed))
  return ()

isNullChecked :: Exp SourcePos -> TcCodeM ()
isNullChecked ( BinOp _ (ExpName _ n@(Name _ EName mPre i)) (Equal _) (Lit _ (Null _)) ) =
    varUpdatedNN n mPre i
isNullChecked ( BinOp _ (Lit _ (Null _)) (Equal _) (ExpName _ n@(Name _ EName mPre i)) ) =
    varUpdatedNN n mPre i
isNullChecked _ = return ()


isNotNullChecked :: Exp SourcePos -> TcCodeM ()
isNotNullChecked ( BinOp _ (ExpName _ n@(Name _ EName mPre i)) (NotEq _) (Lit _ (Null _)) ) =
    varUpdatedNN n mPre i
isNotNullChecked ( BinOp _ (Lit _ (Null _)) (NotEq _) (ExpName _ n@(Name _ EName mPre i)) ) =
    varUpdatedNN n mPre i
isNotNullChecked _ = return ()

