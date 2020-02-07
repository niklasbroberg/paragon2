{-# LANGUAGE TupleSections, BangPatterns, FlexibleInstances, MultiParamTypeClasses, ImpredicativeTypes, PatternGuards #-}
module Language.Java.Paragon.TypeCheck.Monad.TcCodeM
    (
     module Language.Java.Paragon.TypeCheck.Monad.TcDeclM,
     module Language.Java.Paragon.TypeCheck.Monad.CodeEnv,
     module Language.Java.Paragon.TypeCheck.Monad.CodeState,
     module Language.Java.Paragon.TypeCheck.Monad.TcCodeM
{-     TcCodeM, (|||), runTcCodeM,
     getEnv, withEnv,                                  -- Reader
     getState, setState, updateState, mergeWithState,  -- State
     addConstraint,                                    -- Writer

--     withTypeMapAlwaysC,

     setupStartState,

     getPrefix, touchPrefix,

     lookupVar, lookupPrefixName
-}
    ) where

import Language.Java.Paragon.Error
import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.TypeCheck.Monad.TcDeclM

import Language.Java.Paragon.TypeCheck.Monad.CodeEnv
import Language.Java.Paragon.TypeCheck.Monad.CodeState

import Language.Java.Paragon.PolicyLang

import Language.Java.Paragon.TypeCheck.TypeMap
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.NullAnalysis
import Language.Java.Paragon.TypeCheck.Interpreter

import Control.Monad hiding (join)

import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as B

import qualified Control.Monad.Fail as Fail

tcCodeMModule :: String
tcCodeMModule = typeCheckerBase ++ ".Monad.TcCodeM"

-------------------------------------------------
-- All the cool methods of this monad


setupStartState :: TcDeclM CodeState
setupStartState = return emptyCodeState
{-
setupStartState = do
  tm <- getTypeMap
  let aMap = gatherActorInfo tm
      pMap = undefined -- gatherPolicyBounds tm
      iMap = undefined
      tMap = undefined
  return $ CodeState (VarMap aMap pMap iMap tMap) noMods Map.empty
-}
{-
gatherActorInfo :: TypeMap -> ActorMap -- Map Ident (AI { Bool ActorId } )
gatherActorInfo = gatherActorInfo' Nothing

    where gatherActorInfo' mPre tm =
              let acts = Map.assocs $ actors tm -- :: [(Ident, ActorId)]
                  aMap = Map.fromList $ map (mkInfo mPre $ fields tm) acts
                  tMap = gatherActorInfoAux TName mPre
                           (Map.assocs $ Map.map (tMembers . (\(_,_,x) -> x)) $ types tm)
                  pMap = gatherActorInfoAux PName mPre (Map.assocs $ packages tm)
              in foldl1 Map.union [aMap, tMap, pMap]

          mkStab :: VarFieldSig -> Stability
          mkStab (VSig _ _ _ _ final) =
              if final then Stable else FieldV Nothing

          mkInfo :: Maybe (Name ())
                 -> Map (Ident ()) VarFieldSig
                 -> (Ident (), ActorId)
                 -> (Name (), ActorInfo)
          mkInfo mPre fs (i,aid) =
              case Map.lookup i fs of
                Just vti -> (Name () EName mPre i, AI aid (mkStab vti))
                _ -> panic (tcCodeMModule ++ ".gatherActorInfo") $
                     "No field for corresponding actor " ++ show i

          gatherActorInfoAux :: NameType
                             -> Maybe (Name ())
                             -> [(Ident (), TypeMap)]
                             -> Map (Name ()) ActorInfo
          gatherActorInfoAux nt mPre = foldl Map.union Map.empty . map aux
              where aux :: (Ident (), TypeMap) -> Map (Name ()) ActorInfo
                    aux (i,tm) =
                        let pre = Name () nt mPre i
                        in gatherActorInfo' (Just pre) tm

-- TODO: non-final policies should have bounds bottom/top
gatherPolicyBounds :: TypeMap -> Map (Name ()) ActorPolicyBounds
gatherPolicyBounds = gatherPolicyBounds' Nothing

    where gatherPolicyBounds' mPre tm =
              let pols = Map.assocs $ policies tm -- :: [(Ident, PrgPolicy)]
                  aMap = Map.fromList $ map (mkPols mPre $ fields tm)
                         $ map (second RealPolicy) pols
                  tMap = gatherPolicyBoundsAux TName mPre
                           (Map.assocs $ Map.map (tMembers . (\(_,_,x) -> x)) $ types tm)
                  pMap = gatherPolicyBoundsAux PName mPre (Map.assocs $ packages tm)
              in foldl1 Map.union [aMap, tMap, pMap]

          mkPols :: Maybe (Name ())
                 -> Map (Ident ()) VarFieldSig
                 -> (Ident (), ActorPolicy)
                 -> (Name (), ActorPolicyBounds)
          mkPols mPre fs (i,p) =
              case Map.lookup i fs of
                Just _ -> (Name () EName mPre i, KnownPolicy p)
                _ -> panic (tcCodeMModule ++ ".gatherActorInfo") $
                     "No field for corresponding actor " ++ show i

          gatherPolicyBoundsAux :: NameType
                              -> Maybe (Name ())
                              -> [(Ident (), TypeMap)]
                              -> Map (Name ()) ActorPolicyBounds
          gatherPolicyBoundsAux nt mPre = foldl Map.union Map.empty . map aux
              where aux :: (Ident (), TypeMap) -> Map (Name ()) ActorPolicyBounds
                    aux (i,tm) =
                        let pre = Name () nt mPre i
                        in gatherPolicyBounds' (Just pre) tm
-}


-- Running in parallel
infix 1 |||
(|||) :: TcCodeM a -> TcCodeM b -> TcCodeM (a,b)
(TcCodeM f1) ||| (TcCodeM f2) =
    TcCodeM $ \ !te !ts -> do
      (a, !ts1, cs1) <- f1 te ts
      (b, !ts2, cs2) <- f2 te ts
      !ts' <- mergeStatesDeclM ts1 ts2
      return ((a,b), ts', cs1 ++ cs2)


mergeStatesDeclM :: Maybe CodeState -> Maybe CodeState -> TcDeclM (Maybe CodeState)
mergeStatesDeclM (Just s1) (Just s2) = Just <$> mergeStatesDecl s1 s2
mergeStatesDeclM Nothing a = return a
mergeStatesDeclM a Nothing = return a

mergeStatesDecl :: CodeState -> CodeState -> TcDeclM CodeState
mergeStatesDecl s1 s2 = mergeStates s1 s2



--------------------------------------------------
-- The monad used for typechecking code snippets

newtype TcCodeM a =
    TcCodeM (CodeEnv -> Maybe CodeState -> TcDeclM (a, Maybe CodeState, [ConstraintWMsg]))

runTcCodeM :: CodeEnv -> CodeState -> TcCodeM a -> TcDeclM (a, [ConstraintWMsg])
runTcCodeM env state (TcCodeM f) = do
  (a,_,cs) <- f env (Just state)
  return (a, cs)

instance Fail.MonadFail TcCodeM where
  fail err = TcCodeM $ \_ _ -> fail err

instance Monad TcCodeM where
  return x = TcCodeM $ \_ s -> return (x, s, [])

  TcCodeM f >>= h = TcCodeM $ \e s0 -> do
                      (a, s1, cs1) <- f e s0
                      let TcCodeM g = h a
                      (b, s2, cs2) <- g e s1
                      return (b, s2, cs1 ++ cs2)

  fail = Fail.fail

instance Functor TcCodeM where
  fmap = liftM

instance Applicative TcCodeM  where
  (<*>) = ap
  pure = return

instance MonadIO TcCodeM  where
  liftIO = liftTcDeclM . liftIO

instance MonadBase TcCodeM  where
  liftBase = liftTcDeclM . liftBase
  withErrCtxt' ecf (TcCodeM f) = TcCodeM $ \e s -> withErrCtxt' ecf (f e s)
  tryM (TcCodeM f) = TcCodeM $ \e s -> do
                             esa <- tryM $ f e s
                             case esa of
                               Right (a, s', cs) -> return (Right a, s', cs)
                               Left err -> return (Left err, s, [])
  failE = liftTcDeclM . failE
  failEC x = liftTcDeclM . failEC x

instance MonadPR TcCodeM  where
  liftPR = liftTcDeclM . liftPR

--instance MonadTcBaseM TcCodeM where
--  liftTcBaseM = liftTcDeclM . liftTcBaseM
--  withTypeMap tmf (TcCodeM f) = TcCodeM $ \ec e s -> withTypeMap tmf (f ec e s)

instance MonadTcDeclM TcCodeM  where
  liftTcDeclM tdm = TcCodeM $ \_ s -> (,s,[]) <$> tdm
  withCurrentTypeMap tmf (TcCodeM f) = TcCodeM $ \e s -> withCurrentTypeMap tmf (f e s)

instance HasSubTyping TcCodeM where
  subTypeOf rt1 rt2 = liftTcDeclM $ subTypeOf rt1 rt2

instance EvalPolicyM TcCodeM where
  evalPolicy p = do
      debugPrint $ "evalPolicy{TcCodeM}: " ++ prettyPrint p
      interpretPolicy lookupFieldC p
  evalActorId = interpretActorId lookupFieldC
  evalActor = interpretActor lookupFieldC
  evalLock = liftTcDeclM . evalLock

lookupFieldC :: Name SourcePos -> TcCodeM Value
lookupFieldC n@(Name _ _ mPre i) = do
  debugPrint $ "lookupFieldC: " ++ prettyPrint n
  (sty, _, _, _) <- lookupVar mPre i
  case sty of
    TcInstance _ aid _ _ -> return $ VAct aid
    TcPolicyPolT (KnownPolicy (VarPolicy prgp)) -> return $ VPol prgp
    _ -> panic (tcCodeMModule ++ ".lookupFieldC") $
         "Unhandled typemethod lookup: " ++ show sty

-- The environment

getEnv :: TcCodeM CodeEnv
getEnv = TcCodeM (\e s -> return (e,s,[]))

withEnv :: (CodeEnv -> TcDeclM CodeEnv) -> TcCodeM a -> TcCodeM a
withEnv k (TcCodeM f) = TcCodeM $ \e0 s -> do
  e1 <- k e0
  tracePrint ("\n" ++ tcCodeMModule ++ ".withEnv new:\n" ++ formatData e1 ++ "\n")
  r <- f e1 s
  tracePrint ("\n" ++ tcCodeMModule ++ ".withEnv return:\n" ++ formatData e0 ++ "\n")
  return r

getStaticContext :: TcCodeM Bool
getStaticContext = staticContext <$> getEnv

-- The state

getState :: TcCodeM CodeState
getState = do
  ms <- getStateM
  case ms of
    Just s -> return s
    Nothing -> panic (tcCodeMModule ++ ".getState")
               "Calling getState in dead code analysis"

getStateM :: TcCodeM (Maybe CodeState)
getStateM = TcCodeM (\_ s -> return (s,s,[]))

setState :: CodeState -> TcCodeM ()
setState s = TcCodeM (\_ _ -> do
  tracePrint ("\n" ++ tcCodeMModule ++ ".setState:\n" ++ formatData s ++ "\n")
  return ((), Just s, []))

updateState :: (CodeState -> CodeState) -> TcCodeM ()
updateState f = f <$> getState >>= setState

mergeWithState :: CodeState -> TcCodeM ()
mergeWithState s = do
  sOld <- getState
  sNew <- liftTcDeclM $ mergeStatesDecl sOld s
  setState sNew

-- Constraints

addConstraint :: TcConstraint -> Error -> TcCodeM ()
addConstraint c err = TcCodeM (\_ s -> return ((), s, [(c,err)]))




-------------------------------------
-- Working with the VarMap
-------------------------------------


-- Using a zipper technique
touchPrefix :: Maybe (Name SourcePos) -> TcCodeM (VarMap, VarMap -> CodeState)
touchPrefix mn = do
  case mn of
    Nothing -> do
            st <- getState
            return (varMapSt st, \vm -> st { varMapSt = vm })
    Just n@(Name _ nt mPre i) -> do
        (vm, vmf) <- touchPrefix mPre
        case nt of
          _ | nt `elem` [TName, PName] -> do
              let upd newVm = vmf $ vm { typesSt = Map.insert (unIdent i) newVm $ typesSt vm }
              case Map.lookup (unIdent i) $ typesSt vm of
                Just tvm -> return (tvm, upd)
                Nothing -> do setState $ upd emptyVM
                              return (emptyVM, upd)
          EName -> do
              let ist = instanceSt vm
              case Map.lookup (unIdent i) ist of
                Just ii ->
                    let upd newVm =
                            let newII = ii { iMembers = newVm }
                            in vmf $ vm { instanceSt = Map.insert (unIdent i) newII ist }
                    in return (iMembers ii, upd)
                Nothing -> panic (tcCodeMModule ++ ".touchPrefix")
                           $ "Prefix not in state: " ++ show n
          _ -> panic (tcCodeMModule ++ ".touchPrefix")
               $ "Unexpected name: " ++ show n
    _ -> panic (tcCodeMModule ++ ".touchPrefix")
         $ show mn

-- Using a zipper technique
getPrefix :: Maybe (Name SourcePos) -> TcCodeM VarMap
getPrefix mn = do
  case mn of
    Nothing -> varMapSt <$> getState
    Just n@(Name _ nt mPre i) -> do
        !vm <- getPrefix mPre
--        (vm, vmf) <- touchPrefix mPre
        case nt of
          _ | nt `elem` [TName, PName] -> do
              case Map.lookup (unIdent i) $ typesSt vm of
                Just tvm -> return tvm -- , upd)
                Nothing -> do (_, vmf) <- touchPrefix mPre
                              let upd newVm = vmf $ vm { typesSt = Map.insert (unIdent i) newVm $ typesSt vm }
                              setState $ upd emptyVM
                              return emptyVM -- , upd)
          EName -> do
              let ist = instanceSt vm
              case Map.lookup (unIdent i) ist of
                Just ii ->
--                    let upd newVm =
--                            let newII = ii { iMembers = newVm }
--                            in vmf $ vm { instanceSt = Map.insert (unIdent i) newII ist }
--                    in
                      return $ iMembers ii --, upd)
                Nothing -> panic (tcCodeMModule ++ ".getPrefix")
                           $ "Prefix not in state: " ++ show n
          _ -> panic (tcCodeMModule ++ ".getPrefix")
               $ "Unexpected name: " ++ show n
    _ -> panic (tcCodeMModule ++ ".getPrefix")
         $ show mn

-------------------------------
-- | Lookup the prefix part of a name, which has to be dereferenceable.
--   Returns the relevant type (Nothing if package), its typemap
--   and the accumulated policy of the name access path.
--   Last component - if prefix is a field -> is it static
lookupPrefixName :: Name SourcePos -> TcCodeM (Maybe TcStateType, TypeMap, ActorPolicy, Maybe Bool)
lookupPrefixName n@(Name _ EName Nothing i) = do
    -- Special case: This *could* be a var, since those can only
    -- appear first in the name, i.e. prefix == Nothing
    -- We can piggyback on lookupVar since its preconditions are met
    (sty, p, _, mStatFld) <- lookupVar Nothing i
    -- debugPrint $ "lookupPrefixName: " ++ prettyPrint i ++ " :: " ++ prettyPrint sty
    tm <- getTypeMap
    case lookupTypeOfStateT sty tm of
      Right newSig -> do
        -- debugPrint $ prettyPrint newSig
--        debugPrint $ "\nSig before instantiation: "
--                       ++ prettyPrint (tMembers newSig)
--        debugPrint $ "\nSig after  instantiation: "
--                       ++ prettyPrint (instThis p (tMembers newSig)) ++ "\n"
        instTM <- instThis p $ tMembers newSig
        return (Just sty, instTM, p, mStatFld)
      Left (Just err) -> fail err
      _ -> panic (tcCodeMModule ++ ".lookupPrefixName")
           $ "Unknown variable or field: " ++ show n

lookupPrefixName n@(Name _ nt mPre i) = do
  baseTm <- getTypeMap
  (mPreSty, preTm, prePol, mStatFld) <-
    case mPre of
      Nothing -> do
                bt <- bottomM
                return (Nothing, baseTm, bt, Nothing)
      Just pre -> lookupPrefixName pre
  baseTm2 <- getTypeMap
  case nt of
    EName -> case Map.lookup (unIdent i) $ fields preTm of
               Just (VSig ty p _ _ _ nnf) -> do
                   -- debugPrint $ "lookupPrefixName: EName: " ++ prettyPrint n ++
                   --               " :: " ++ prettyPrint ty
                   -- debugPrint $ show (packages baseTm2) ++ "\n"
                   sty <- getStateType (Just n) mPreSty ty
                   when (nnf && nullableFromStateType sty) (
                                                              do
                                                                _ <- updateStateType (Just (n, True)) ty (Just (setNullInStateType sty (NotNull, Free)))
                                                                return ())
                   _sty <- getStateType (Just n) mPreSty ty
                   case lookupTypeOfStateT _sty baseTm2 of
                     Right tsig -> do rPol <- prePol `lub` p
                                      instTM <- instThis p $ tMembers tsig
                                      return (Just _sty, instTM, rPol, mStatFld)
                     Left (Just err) -> fail err
                     _ -> panic (tcCodeMModule ++ ".lookupPrefixName")
                          $ "Unknown type: " ++ show ty
               Nothing -> panic (tcCodeMModule ++ ".lookupPrefixName")
                          $ "Not a field: " ++ show n

    TName -> do
            (_tps, _iaps, tsig) <- case Map.lookup (unIdent i) $ types preTm of
                                     Nothing -> liftTcDeclM $ fetchType n
                                     -- panic (tcCodeMModule ++ ".lookupPrefixName")
                                     -- - $ "Not a type: " ++ show n
                                     Just tinfo -> return tinfo
-- This lookup arises from refering to static fields, and then type arguments aren't given.
-- TODO: Check that field *is* static.
--            check (null tps) $
--                      "Type " ++ prettyPrint n ++ " expects " ++
--                      show (length tps) ++ " but has been given none."
            return (Just . stateType . TcRefT $ tType tsig, tMembers tsig, prePol, mStatFld)

    PName -> case Map.lookup (unIdent i) $ packages preTm of
               Nothing -> do liftTcDeclM $ fetchPkg n
                             return (Nothing, emptyTM, prePol, mStatFld)
               -- panic (tcCodeMModule ++ ".lookupPrefixName")
                          -- - $ "Not a package: " ++ show n
               Just tm -> return (Nothing, tm, prePol, mStatFld)

    _ -> panic (tcCodeMModule ++ ".lookupPrefixName")
         $ "Malformed prefix name: " ++ show n

lookupPrefixName n = panic (tcCodeMModule ++ ".lookupPrefixName")
                     $ "Malformed prefix name: " ++ show n


-- | Lookup the type and policy of a field or variable access path.
--   Last component - if it is a field -> is it static
--   Precondition: Name is the decomposition of an EName
lookupVar :: Maybe (Name SourcePos) -> Ident SourcePos -> TcCodeM (TcStateType, ActorPolicy, Bool, Maybe Bool)
lookupVar Nothing i@(Ident sp _) = do
  -- Could be a single variable
  let nam = Name sp EName Nothing i -- Reconstructing for lookups
  varMaps <- vars <$> getEnv
  case lookupVarInVarMaps i varMaps of
    -- Is a variable
    Just (VSig ty p param _ _ _) -> do
                             sty <- getStateType (Just nam) Nothing ty
                             --debugPrint $ "%%% " ++ prettyPrint i ++ " is a variable!"
                             --debugPrint $ prettyPrint ty
                             return (sty, p, param, Nothing)
    -- Not a variable, must be a field
    Nothing -> do
      tm <- getTypeMap
      case Map.lookup (unIdent i) $ fields tm of
        Just (VSig ty p param statFld _ _) -> do
                  sty <- getStateType (Just nam) Nothing ty
                  debugPrint $ "Var: " ++ prettyPrint i ++ " " ++ show (sty, p)
                  return (sty, p, param, Just statFld)
        Nothing ->
            -- We could be in actor resolution mode, in which case the field is not yet registered,
            -- except as an actor identity
            case Map.lookup (unIdent i) $ actors tm of
              Just aid -> do
                 let pnc = panic (tcCodeMModule ++ ".lookupVar:actors")
                             $ "Not a var or field, but an actor, and yet...: " ++ show i
                 -- Really ugly hack where we assume that only the actor id will be unwrapped
                 -- at the use site
                 let sty = TcInstance pnc aid pnc pnc
                 return (sty, pnc, pnc, pnc)
              Nothing -> panic (tcCodeMModule ++ ".lookupVar")
                         $ "Not a var or field: " ++ show i
  where lookupVarInVarMaps :: Ident a -> [Map B.ByteString VarFieldSig] -> Maybe VarFieldSig
        lookupVarInVarMaps _ [] = Nothing
        lookupVarInVarMaps i (varMap:varMaps) =
          case Map.lookup (unIdent i) varMap of
            Nothing     -> lookupVarInVarMaps i varMaps
            varFieldSig -> varFieldSig

lookupVar (Just pre) i@(Ident sp _) = do
  (mPreTy, preTm, prePol, _) <- lookupPrefixName pre
  x <- liftIO checkNull
  when ((case mPreTy of
           Just st | maybeNull st -> True
           _ -> False) && x) throwNull
  case Map.lookup (unIdent i) $ fields preTm of
    Just (VSig ty p _ statFld _ _) -> do
      let nam = Name sp EName (Just pre) i
        --debugPrint $ "lookupVar: " ++ prettyPrint nam ++ " :: " ++ prettyPrint ty
        --debugPrint $ "   mPreTy: " ++ show mPreTy
      sty <- getStateType (Just nam) mPreTy ty
      rPol <- prePol `lub` p
      return (sty, rPol, False, Just statFld)
    Nothing -> do
      case mPreTy of
        Just preTy -> fail $ "Type " ++ prettyPrint preTy ++
                      " does not have a field named " ++ prettyPrint i
        Nothing -> panic (tcCodeMModule ++ ".lookupVar")
                   $ "EName as direct child of PName: "
                         ++ show (Name sp EName (Just pre) i)

--------------------------------------------
--          Working with states           --
--------------------------------------------
{-
-- Leave actor mappings from fields
startState :: TcCodeM ()
startState = updateState $ \s -> s { lockMods = noMods, exnS = Map.empty }
-}

-- Instance analysis

-- | Looks up the type of the provided location (if any). For actors, the
-- associated type of that (instance) actor is returned. For policies the
-- policy bounds. For all other types just the type with null-pointer
-- information.
getStateType :: Maybe (Name SourcePos)          -- ^ field/var name (if decidable)
             -> Maybe TcStateType        -- ^ containing object state type
             -> TcType                   -- ^ field/var/cell type
             -> TcCodeM TcStateType
getStateType mn mtyO ty
--    | ty == actorT   = do actorIdT <$> getActorId mn mtyO
    | ty == policyT  = do policyPolT <$> getPolicyBounds mn mtyO
    | Just ct <- mClassType ty = do
                   (aid, as, nt) <- getInstanceActors ct mn mtyO
                   return $ instanceT (TcClsRefT ct) aid as nt
    | otherwise = return $ stateType ty

{-
getActorId :: Maybe (Name SourcePos)
           -> Maybe TcStateType
           -> TcCodeM ActorIdSpec
getActorId Nothing Nothing = ConcreteActorId <$> liftTcDeclM unknownActorId
getActorId (Just (Name _ EName mPre i)) mstyO = do
  -- Check if already exists:
  (vm, upd) <- touchPrefix mPre -- Prefix guaranteed to exist
  let ast = actorSt vm
  case Map.lookup (unIdent i) ast of
    Just ai -> return $ aID ai
    Nothing -> do
        tm <- case mstyO of
                Just styO -> do
                           tsig <- lookupTypeOfStateType styO
                           return $ tMembers tsig
                Nothing -> getTypeMap
        (stab, aid) <- case Map.lookup (unIdent i) $ actors tm of
                         Just aid -> return (True, aid)
                         Nothing -> do
                           newAid <- ConcreteActorId <$> liftTcDeclM unknownActorId
                           return (False, newAid)
        let ai = AI stab aid
        setState $ upd $ vm { actorSt = Map.insert (unIdent i) ai ast }
        return aid
getActorId mn ms = panic (tcCodeMModule ++ ".getActorId")
                   $ show (mn, ms)
-}
getPolicyBounds :: Maybe (Name SourcePos)
                -> Maybe TcStateType
                -> TcCodeM ActorPolicyBounds
getPolicyBounds Nothing Nothing = PolicyBounds <$> bottomM <*> topM
getPolicyBounds (Just (Name _ EName mPre i)) mstyO = do
  (vm, upd) <- touchPrefix mPre -- Prefix guaranteed to exist
  let pst = policySt vm
  case Map.lookup (unIdent i) pst of
  -- Check if already exists:
    Just pif -> return $ pBounds pif
    Nothing -> do
        tm <- case mstyO of
                Just styO -> do
                           debugPrint $ "getPolicyBounds: " ++ show styO
                           tsig <- lookupTypeOfStateType styO
                           return $ tMembers tsig
                Nothing -> getTypeMap
        (stab, pbs) <- case Map.lookup (unIdent i) $ policies tm of
                         Just pol -> return (True, KnownPolicy $ VarPolicy pol)
                         Nothing -> do
                              bt <- bottomM
                              tp <- topM
                              return (False, PolicyBounds bt tp)
        let pif = PI stab pbs
        setState $ upd $ vm { policySt = Map.insert (unIdent i) pif pst }
        return pbs
getPolicyBounds mn ms = panic (tcCodeMModule ++ ".getPolicyBounds")
                        $ show (mn, ms)


getInstanceActors :: TcClassType
                  -> Maybe (Name SourcePos)
                  -> Maybe TcStateType
                  -> TcCodeM (TypedActorIdSpec, [TypedActorIdSpec], NullType)
getInstanceActors ct@(TcClassT tyN _) Nothing Nothing = do
  (iaps, _) <- lookupTypeOfType (clsTypeToType ct)
  aid <- TypedActorIdSpec (TcClsRefT ct) . ConcreteActorId <$> unknownActorId
  ac <- mapM (\(rt,s) -> do
                rTy <- evalSrcRefType genBot rt
                aid <- instanceActorId $ Name defaultPos EName (Just tyN) $ Ident defaultPos s
                return $ TypedActorIdSpec rTy $ ConcreteActorId aid) iaps
  return (aid, ac, (MaybeNull, Free))

getInstanceActors ct@(TcClassT tyN _) (Just (Name sp EName mPre i)) mstyO = do
  vm <- getPrefix mPre -- Prefix guaranteed to exist
  let ist = instanceSt vm
  debugPrint $ "Instance state: " ++ show ist
  -- Check if already exists:
  case Map.lookup (unIdent i) ist of
    Just ii -> return (iActorId ii, iImplActorArgs ii, iNull ii)
    Nothing -> do
        tm <- case mstyO of
                Just styO -> do
                           debugPrint $ "styO: " ++ show styO
                           tsig <- lookupTypeOfStateType styO
                           return $ tMembers tsig
                Nothing -> debugPrint "No mstyO!" >> getTypeMap
        (stab, aid, aids) <-
            case Map.lookup (unIdent i) $ fields tm of
              Just (VSig ty _ _ _ fin _) -> do
                (iaps, _) <- lookupTypeOfType ty
                aid  <- case Map.lookup (unIdent i) $ actors tm of
                          Just a -> return a
                          Nothing -> TypedActorIdSpec (TcClsRefT ct) . ConcreteActorId <$> unknownActorId
                aids <- mapM (\(rt,s) -> do
                                rTy <- evalSrcRefType genBot rt
                                aid <- instanceActorId $ Name sp EName (Just tyN) $ Ident sp s
                                return $ TypedActorIdSpec rTy $ ConcreteActorId aid) iaps
                return (fin, aid, aids)
              Nothing -> do
                --debugPrint $ prettyPrint tm
                panic (tcCodeMModule ++ ".getInstanceActors")
                          $ "No such field: " ++ prettyPrint ct ++ "." ++ prettyPrint i
        let ii = II (TcClsRefT ct) stab False -- TODO: Freshness
                   aid aids emptyVM (MaybeNull, Free)    --TODO: Really ?
        --debugPrint $ "Forced to touch"
        (_, upd) <- touchPrefix mPre
        setState $ upd $ vm { instanceSt = Map.insert (unIdent i) ii ist }
        return (aid, aids, (MaybeNull, Free))    --TODOY Still sure of you ?
getInstanceActors ct mn ms = panic (tcCodeMModule ++ ".getPolicyBounds")
                             $ show (ct, mn, ms)

throwNull :: TcCodeM ()
throwNull = do
   (_rX, wX) <- lookupExn nullExnT
   -- Check E[branchPC](X) <= E[exns](X)[write]
   bpc <- getBranchPC (exnE nullExnT)
   constraintPC bpc wX $ \p src -> toUndef $
     "Exception with write effect " ++ prettyPrint wX ++
     " may not be thrown in " ++ src ++
     " with write effect bound " ++ prettyPrint p
   -- Check exnPC(S) <= E[exns](X)[write]
   epc <- getExnPC
   constraintPC epc wX $ \p src -> toUndef $
     "Exception with write effect " ++ prettyPrint wX ++
     " may not be thrown in " ++ src ++
     " with write effect bound " ++ prettyPrint p
   throwExn (ExnType nullExnT) wX


updateStateType :: Maybe (Name SourcePos, Bool) -- field/var name and stability (if decidable)
                -> TcType                -- field/var/cell type
                -> Maybe TcStateType     -- rhs state type (Nothing if no initialiser)
                -> TcCodeM TcStateType
--updateStateType mN tyV mRhsSty
--    | tyV == actorT = actorIdT <$> updateActorId mN mRhsSty
updateStateType mN tyV mRhsSty
    | tyV == policyT = policyPolT <$> updatePolicyBounds mN mRhsSty
updateStateType mN tyV mRhsSty
    | Just ct <- mClassType tyV = do
                   debugPrint $ "updateStateType[instance]: " ++ show mN
                   (aid, as, nt) <- updateInstanceActors ct mN mRhsSty
                   return $ instanceT (TcClsRefT ct) aid as nt
updateStateType _ tyV _ = return $ stateType tyV
{-
updateActorId :: Maybe (Name SourcePos, Bool) -- field/var name and stability (if decidable)
              -> Maybe TcStateType     -- rhs state type (Nothing if no initialiser)
              -> TcCodeM ActorIdSpec
updateActorId Nothing (Just rhsSty) =
    case mActorId rhsSty of
      Just aid -> return aid
      Nothing -> panic (tcCodeMModule ++ ".updateActorId")
                 $ "Non-actor rhs for actor field: " ++ show rhsSty
updateActorId (Just (Name _ EName mPre i, stab)) mRhsSty = do
  (vm, upd) <- touchPrefix mPre
  aid <- case mRhsSty of
           Nothing -> liftTcDeclM $ ConcreteActorId <$> freshActorId (prettyPrint i)
           Just sty | Just aid <- mActorId sty -> return aid
           Just _ -> panic (tcCodeMModule ++ ".updateActorId")
                     $ "Non-actor rhs for actor field: " ++ show mRhsSty
  setState $ upd $ vm { actorSt = Map.insert (unIdent i) (AI stab aid) $ actorSt vm }
  return aid
updateActorId mn _ = panic (tcCodeMModule ++ ".updateActorId")
                     $ show mn
-}
updatePolicyBounds :: Maybe (Name SourcePos, Bool) -- field/var name and stability (if decidable)
                   -> Maybe TcStateType     -- rhs state type (Nothing if no initialiser)
                   -> TcCodeM ActorPolicyBounds
updatePolicyBounds Nothing (Just rhsSty) =
    case mPolicyPol rhsSty of
      Just pbs -> return pbs
      Nothing -> panic (tcCodeMModule ++ ".updatePolicyBounds")
                 $ "Non-policy rhs for policy field: " ++ show rhsSty
updatePolicyBounds (Just (Name _ EName mPre i, stab)) mRhsSty = do
  (vm, upd) <- touchPrefix mPre
  pbs <- case mRhsSty of
           Nothing -> topM >>= \tp -> return $ KnownPolicy tp -- default for "primitive" policy types
           Just sty | Just pbs <- mPolicyPol sty -> return pbs
           Just _ -> panic (tcCodeMModule ++ ".updatePolicyBounds")
                     $ "Non-policy rhs for policy field: " ++ show mRhsSty
  setState $ upd $ vm { policySt = Map.insert (unIdent i) (PI stab pbs) $ policySt vm }
  return pbs
updatePolicyBounds mn _ = panic (tcCodeMModule ++ ".updatePolicyBounds")
                          $ show mn


updateInstanceActors :: TcClassType
                     -> Maybe (Name SourcePos, Bool) -- field/var name and stability (if decidable)
--                     -> Maybe TcStateType     -- containing type
                     -> Maybe TcStateType     -- rhs state type (Nothing if no initialiser)
                     -> TcCodeM (TypedActorIdSpec, [TypedActorIdSpec], NullType)
updateInstanceActors ct Nothing (Just rhsSty) = do
--     debugPrint $ "updateInstanceActors Nothing: " ++ show (ct, rhsSty)
    case mInstanceType rhsSty of
      Just (_, aid, aids, nt) -> return (aid, aids, nt)
      Nothing | isNullType rhsSty -> getInstanceActors ct Nothing Nothing
      Nothing -> panic (tcCodeMModule ++ ".updateInstanceActors")
                 $ "Non-instance rhs for class type field: " ++ show rhsSty
updateInstanceActors ct@(TcClassT tyN _) (Just (_n@(Name _ EName mPre i), stab)) mRhsSty = do
  debugPrint $ "updateInstanceActors Just: " ++ show (prettyPrint _n, stab, prettyPrint ct, fmap prettyPrint mRhsSty)
  (vm, upd) <- touchPrefix mPre
  (aid, iaas, iint) <- case mRhsSty of
            Nothing -> do
              (iaps, _) <- lookupTypeOfType (clsTypeToType ct)
              aid <- TypedActorIdSpec (TcClsRefT ct) . ConcreteActorId <$> unknownActorId
              as <- mapM (\(rt,s) -> do
                            rTy <- evalSrcRefType genBot rt
                            aid <- instanceActorId $ Name defaultPos EName (Just tyN) $ Ident defaultPos s
                            return $ TypedActorIdSpec rTy $ ConcreteActorId aid) iaps
              return (aid, as, (MaybeNull, Free))
            Just sty | Just (_, aid, aids, nt) <- mInstanceType sty -> return (aid, aids, nt)
                     | isNullType sty ->
                         getInstanceActors ct Nothing Nothing
            Just _ -> panic (tcCodeMModule ++ ".updateInstanceActors")
                      $ "Non-instance rhs for class type field: " ++ show mRhsSty
  let ist = instanceSt vm
  ii <- case Map.lookup (unIdent i) ist of
          Just ii -> return ii { iNull = iint }
          Nothing ->
            return $ II (TcClsRefT ct) stab False -- TODO: Freshness
                         aid iaas emptyVM iint

  setState $ upd $ vm { instanceSt = Map.insert (unIdent i) ii ist }
  return (aid, iaas, iint)
updateInstanceActors _ mn _ = panic (tcCodeMModule ++ ".updateInstanceActors")
                                $ show mn

lookupExn :: TcType -> TcCodeM (ActorPolicy, ActorPolicy)
lookupExn tyX = do
  debugPrint ":: In lookupExn"
  exnMap <- exnsE <$> getEnv
  case Map.lookup tyX exnMap of
    Just ps -> return ps
    Nothing -> fail $ "lookupExn: Unregistered exception type: " ++ prettyPrint tyX

registerExn_ :: TcType -> PrgPolicy -> PrgPolicy -> TcCodeM a -> TcCodeM a
registerExn_ tyX rX wX = registerExn tyX (VarPolicy rX) (VarPolicy wX)

registerExn :: TcType -> ActorPolicy -> ActorPolicy -> TcCodeM a -> TcCodeM a
registerExn tyX rX wX = registerExns [(tyX, (rX,wX))]

registerExns :: [(TcType, (ActorPolicy, ActorPolicy))] -> TcCodeM a -> TcCodeM a
registerExns tysPols =
    withEnv $ \env ->
        let oldMap = exnsE env
            newMap = foldl (\m (t,ps) -> Map.insert t ps m) oldMap tysPols
        in return $ env { exnsE = newMap }


extendLockEnv :: [TcLock] -> TcCodeM a -> TcCodeM a
extendLockEnv locs = withEnv $ \env ->
                        return $ env { lockstate = lockstate env
                                          ||>> openAll (map skolemizeLock locs) }

getBranchPC :: Entity -> TcCodeM [(ActorPolicy, String)]
getBranchPC e = do env <- getEnv
                   -- debugTcCodeM $ "Env: " ++ show env
                   return $ branchPC (Just e) env

getBranchPC_ :: TcCodeM [(ActorPolicy, String)]
getBranchPC_ = do env <- getEnv
                  return $ branchPC Nothing env

extendBranchPC :: ActorPolicy -> String -> TcCodeM a -> TcCodeM a
extendBranchPC p str = withEnv $ return . joinBranchPC p str

addBranchPCList :: [Ident SourcePos] -> TcCodeM a -> TcCodeM a
addBranchPCList is =
    withEnv $ \env ->
        let (bm, def) = branchPCE env
            newBm = foldl (\m i -> Map.insert (VarEntity (mkSimpleName EName i)) [] m) bm is
        in return $ env { branchPCE = (newBm, def) }

addBranchPC :: Entity -> TcCodeM a -> TcCodeM a
addBranchPC ent =
    withEnv $ \env ->
        let (bm, def) = branchPCE env
            newBm = Map.insert ent [] bm
        in return $ env { branchPCE = (newBm, def) }

getCurrentPC :: Entity -> TcCodeM ActorPolicy
getCurrentPC ent = do
  bpcs <- map fst <$> getBranchPC ent
  epcs <- map fst <$> getExnPC
  bt <- bottomM
  foldM lub bt (bpcs ++ epcs)

registerParamType :: Ident SourcePos -> TcType -> TcCodeM ()
registerParamType i ty = registerStateType i ty True Nothing

--------------------------------------------
--       Working with constraints         --
--------------------------------------------

constraint :: TcLockSet -> ActorPolicy -> ActorPolicy -> Error -> TcCodeM ()
constraint (LockSet ls) p q err = do -- addConstraint $ LRT ls p1 p2
  g <- getGlobalLockProps
  -- bs <- getParamPolicyBounds
  eBC <- lrtC g ls p q
  case eBC of
    Left b -> do
      _ <- getState
      checkC b err -- "State: " ++ show st -- undefined -- (err {-++ "\n\nState: " ++ show st -})
    Right c -> addConstraint c err

getParamPolicyBounds :: TcCodeM [(B.ByteString, ActorPolicy)]
getParamPolicyBounds = parBounds <$> getEnv

getGlobalLockProps :: TcCodeM GlobalPol
getGlobalLockProps = do
  cs <- go <$> getTypeMap
  return cs
      where go :: TypeMap -> GlobalPol
            go tm = let lps = map lProps $ Map.elems $ locks tm
                        tlps = map (go . tMembers . (\(_,_,x) -> x)) $ Map.elems $ types tm
                        plps = map go $ Map.elems $ packages tm
                    in concat $ lps ++ tlps ++ plps

locksToRec :: [TcLock] -> LockProp
locksToRec ls = undefined --TcPolicy (map (\x -> TcClause x []) (map lockToAtom ls))

constraintLS :: ActorPolicy -> ActorPolicy -> Error -> TcCodeM ()
constraintLS p1 p2 err = do
  l <- getCurrentLockState
  withErrCtxt (LockStateContext (prettyPrint l)) $
    constraint l p1 p2 err

constraintPC :: [(ActorPolicy, String)] -> ActorPolicy -> (ActorPolicy -> String -> Error) -> TcCodeM ()
constraintPC bpcs pW msgf = mapM_ (uncurry constraintPC_) bpcs
    where constraintPC_ ::  ActorPolicy -> String -> TcCodeM ()
          -- Don't take lock state into account
          constraintPC_ pPC src = constraint emptyLockSet pPC pW (msgf pPC src)



exnConsistent :: Either (Name SourcePos) TcClassType
              -> TcType -> (ActorPolicy, ActorPolicy) -> TcCodeM ()
exnConsistent caller exnTy (rX,wX) = do
    exnMap <- exnsE <$> getEnv
    --debugTc $ "Using exnMap: " ++ show exnMap
    let (callerName, callerSort) =
            case caller of
              Left n   -> (prettyPrint n , "method"     )
              Right ct -> (prettyPrint ct, "constructor")
    case Map.lookup exnTy exnMap of
      Nothing -> fail $ "Unchecked exception: " ++ prettyPrint (typeName_ exnTy)
      Just (rE, wE) -> do
        constraint emptyLockSet wE wX $ toUndef $
                    "Exception " ++ prettyPrint exnTy ++ ", thrown by invocation of " ++
                    callerSort ++ " " ++ callerName ++ ", has write effect " ++
                    prettyPrint wX ++
                    " but the context in which the " ++ callerSort ++
                    " is invoked expects its write effect to be no less restrictive than " ++
                    prettyPrint wE
        constraint emptyLockSet rX rE $ toUndef $ -- constraintLS?
                    "Exception " ++ prettyPrint exnTy ++ ", thrown by invocation of " ++
                    callerSort ++ " " ++ callerName ++ ", has policy " ++ prettyPrint rX ++
                    " but the context in which the " ++ callerSort ++
                    " is invoked expects its policy to be no more restrictive than " ++
                    prettyPrint rE



------------------------------------------------------------
getExnPC :: TcCodeM [(ActorPolicy, String)]
getExnPC = exnPC <$> getState

throwExn :: ExnType -> ActorPolicy -> TcCodeM ()
throwExn et pX = do
  debugPrint $ "throwExn: " ++ show et
  state <- getState
  let !oldXmap = exnS state
      newXmap = Map.fromList [(et, ExnPoint state pX)]
  mergedXmap <- liftTcDeclM $ mergeExns oldXmap newXmap
  setState $ state { exnS = mergedXmap }

deactivateExn :: ExnType -> TcCodeM ()
deactivateExn et =
    updateState $ \s ->
        let oldEmap = exnS s
            newEmap = Map.delete et oldEmap
        in s { exnS = newEmap }


activateExns :: [(ExnType, (ActorPolicy, LockMods))] -> TcCodeM ()
activateExns exns = do
  state <- getState
  let (ts, sigs) = unzip exns
      xPoints = map (\(wX, modsX) ->
                     let !s = -- scramble $ -- FullV should be Nothing - TODO
                               state { lockMods = lockMods state ++>> modsX }
                     in (s, wX)) sigs
  let -- oldXmap = exnS state
      newXmap = Map.fromList $ zip ts (map (uncurry ExnPoint) xPoints)
  !mergedXmap <- liftTcDeclM $ mergeExns (exnS state) newXmap
  setState $ state { exnS = mergedXmap }

getExnState :: ExnType -> TcCodeM (Maybe CodeState)
getExnState et = do
  eMap <- exnS <$> getState
  return $ epState <$> Map.lookup et eMap

mergeActiveExnStates :: TcCodeM ()
mergeActiveExnStates = do
  exnMap <- exnS <$> getState
  mapM_ (mergeWithState . epState) $ Map.elems exnMap

useExnState :: CodeState -> TcCodeM ()
useExnState es = updateState (\s -> s { exnS = exnS es })

getCurrentLockState :: TcCodeM TcLockSet
getCurrentLockState = do
  base <- lockstate <$> getEnv
  mods <- lockMods <$> getState
  return $ base ||>> mods

applyLockMods :: LockMods -> TcCodeM ()
applyLockMods lms = do
  updateState $ \s -> s { lockMods = lockMods s ++>> lms }

openLock, closeLock :: TcLock -> TcCodeM ()
openLock  l = applyLockMods $ open  $ skolemizeLock l
closeLock l = applyLockMods $ close $ skolemizeLock l


registerStateType :: Ident SourcePos               -- Entity to register
                  -> TcType                 -- Its type
                  -> Bool                   -- Its stability
                  -> Maybe TcStateType      -- rhs state type (Nothing if no initialiser)
                  -> TcCodeM ()
registerStateType i@(Ident sp _) tyV stab mRhsSty = ignore $ updateStateType (Just (Name sp EName Nothing i, stab)) tyV mRhsSty


isCompileTime :: TcCodeM Bool
isCompileTime = compileTime <$> getEnv

withCompileTimeStatus :: Bool -> TcCodeM a -> TcCodeM a
withCompileTimeStatus b = withEnv (\env -> return $ env { compileTime = b })
