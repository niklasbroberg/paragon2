{-# LANGUAGE DeriveDataTypeable #-}
module Language.Java.Paragon.TypeCheck.Monad.CodeState
    (
     module Language.Java.Paragon.TypeCheck.Monad.CodeState,
     ActorPolicyBounds(..), ActorPolicy
    ) where

import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction

import Language.Java.Paragon.PolicyLang
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.NullAnalysis

import Language.Java.Paragon.TypeCheck.Monad.TcDeclM

import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as B
import Data.List (intersect, union)
import Data.Maybe (fromJust, catMaybes)
import Control.Monad (zipWithM)

import Data.Data

codeStateModule :: String
codeStateModule = typeCheckerBase ++ ".Monad.CodeState"

data VarMap = VarMap {
--      actorSt    :: !ActorMap,
      policySt   :: !PolicyMap,
      instanceSt :: !InstanceMap,  -- ^ Non-static fields and variables
      typesSt    :: !TypesMap      -- ^ Static fields
    }
  deriving (Eq, Show, Data, Typeable)

emptyVM :: VarMap
emptyVM = VarMap {-Map.empty-} Map.empty Map.empty Map.empty

data CodeState = CodeState {
      varMapSt   :: !VarMap,
      lockMods   :: !LockMods,
      exnS       :: !ExnsMap
    }
  deriving (Eq, Show, Data, Typeable)

emptyCodeState :: CodeState
emptyCodeState = CodeState emptyVM noDelta Map.empty

data InstanceInfo = II {
      iType :: TcRefType,
      iStable :: Bool,
      iFresh :: Bool,
      iActorId :: TypedActorIdSpec,
      iImplActorArgs :: [TypedActorIdSpec],
      iMembers :: !VarMap,
      iNull :: !NullType
    }
  deriving (Eq, Show, Data, Typeable)

--data ActorInfo = AI { aStable :: Bool, aID :: ActorIdSpec }
--  deriving (Eq, Show, Data, Typeable)

data PolicyInfo = PI { pStable :: Bool, pBounds :: ActorPolicyBounds }
  deriving (Eq, Show, Data, Typeable)

--type ActorMap    = Map.Map B.ByteString ActorInfo
type PolicyMap   = Map.Map B.ByteString PolicyInfo
type InstanceMap = Map.Map B.ByteString InstanceInfo
type TypesMap    = Map.Map B.ByteString VarMap

------------------------------------------
-- Getting information
------------------------------------------

{-
getCSActorId :: CodeState -> Name () -> Maybe ActorId
getCSActorId st n = aID <$> getGeneric (varMapSt st) actorSt n

getCSPolicyBounds :: CodeState -> Name () -> Maybe ActorPolicyBounds
getCSPolicyBounds st n = pBounds <$> getGeneric (varMapSt st) policySt n

getCSImplActorArgs :: CodeState -> Name () -> Maybe [ActorId]
getCSImplActorArgs st n = iImplActorArgs <$> getGeneric (varMapSt st) instanceSt n

getCSFresh :: CodeState -> Name () -> Maybe Bool
getCSFresh st n = iFresh <$> getGeneric (varMapSt st) instanceSt n

getGeneric :: VarMap -> (VarMap -> Map.Map (Ident ()) a) -> Name () -> Maybe a
getGeneric vm leafMap n =
    case n of
      Name _ EName mPre i -> do
             preVm <- getGenericPre mPre
             Map.lookup i $ leafMap preVm
      _ -> panic (codeStateModule ++ ".getGeneric")
           $ "Unexpected name: " ++ show n

    where getGenericPre :: Maybe (Name ()) -> Maybe VarMap
          getGenericPre Nothing = return vm
          getGenericPre (Just (Name _ nt mPre i)) = do
              preVm <- getGenericPre mPre
              case nt of
                TName ->              Map.lookup i (typesSt    preVm)
                EName -> iMembers <$> Map.lookup i (instanceSt preVm)
                _ -> panic (codeStateModule ++ ".getGenericPre")
                     $ "Unexpected name type: " ++ show n
          getGenericPre _ = panic (codeStateModule ++ ".getGenericPre")
                            $ show n
-}
------------------------------------------
-- Scrambling of state
------------------------------------------
------------------------------------------
-- Merging of states in parallel
------------------------------------------

mergeVarMaps :: VarMap -> VarMap -> TcDeclM VarMap
mergeVarMaps (VarMap {-as1-} ps1 is1 ts1) (VarMap {-as2-} ps2 is2 ts2) = do
--  newActors <- mergeActors    as1 as2
  newPols   <- mergePolicies  ps1 ps2
  newInsts  <- mergeInstances is1 is2
  newTypes  <- mergeTypesMaps ts1 ts2
  return $ VarMap {-newActors-} newPols newInsts newTypes

--mergeStates :: Uniq -> CodeState -> CodeState -> IO CodeState
mergeStates :: CodeState -> CodeState -> TcDeclM CodeState
mergeStates (CodeState vm1 ls1 es1) (CodeState vm2 ls2 es2) = do
  newVm    <- mergeVarMaps vm1 vm2
  newExns  <- mergeExns    es1 es2
  let newState = CodeState {
               varMapSt = newVm,
               lockMods = ls1 <++> ls2,
               exnS     = newExns
             }
  tracePrint ("\n" ++ codeStateModule ++ ".mergeStates:\n" ++ formatData newState ++ "\n")
  return newState

------------------------------------------
-- Instance tracking
------------------------------------------

mergeGeneric :: Ord k => (v -> v -> TcDeclM v)
             -> Map.Map k v -> Map.Map k v -> TcDeclM (Map.Map k v)
mergeGeneric mergeVals m1 m2 = do
  let newKeys = Map.keys m1 `intersect` Map.keys m2
      oldVals = map (\k -> (fromJust (Map.lookup k m1), fromJust (Map.lookup k m2))) newKeys
  newVals <- mapM (uncurry mergeVals) oldVals
  return $ Map.fromList $ zip newKeys newVals


mergeInstances :: InstanceMap -> InstanceMap -> TcDeclM InstanceMap

mergeInstances m1 m2 = do --mergeGeneric mergeIInfos
  let newKeys = Map.keys m1 `intersect` Map.keys m2
      oldVals = map (\k -> (k, fromJust (Map.lookup k m1), fromJust (Map.lookup k m2))) newKeys
  newKeyVals <- mapM mergeIInfos oldVals
  return $ Map.fromList $ catMaybes newKeyVals
        where mergeIInfos :: (B.ByteString, InstanceInfo, InstanceInfo) -> TcDeclM (Maybe (B.ByteString, InstanceInfo))
              mergeIInfos (k,ii1,ii2) = do
                if iType ii1 /= iType ii2
                 then return Nothing
                 else do
                   aid <- mergeIa (iActorId ii1) (iActorId ii2)
                   as <- mergeIas (iImplActorArgs ii1) (iImplActorArgs ii2)
                   newMems <- mergeVarMaps (iMembers ii1) (iMembers ii2)
                   newNull <- mergeNullTypes (iNull ii1) (iNull ii2)
                   return $ Just (k, II
                                       (iType ii1)
                                       (iStable ii1)
                                       (iFresh ii1 && iFresh ii2)
                                       aid as newMems newNull)

              mergeIas :: [TypedActorIdSpec] -> [TypedActorIdSpec] -> TcDeclM [TypedActorIdSpec]
              mergeIas ias1 ias2 = zipWithM mergeIa ias1 ias2

              mergeIa :: TypedActorIdSpec -> TypedActorIdSpec -> TcDeclM TypedActorIdSpec
              mergeIa ai1 ai2
                  | ai1 == ai2 = return ai1
              mergeIa (TypedActorIdSpec rt (ConcreteActorId (Instance n _))) _
                  = TypedActorIdSpec rt . ConcreteActorId <$> newInstance n
              mergeIa _ (TypedActorIdSpec rt (ConcreteActorId (Instance n _)))
                  = TypedActorIdSpec rt . ConcreteActorId <$> newInstance n
              mergeIa (TypedActorIdSpec rt (ConcreteActorId (Unknown _))) _
                  = TypedActorIdSpec rt . ConcreteActorId <$> newUnknown
              mergeIa ai _ = panic (codeStateModule ++ ".mergeIas")
                             $ "Instance has non-instance implicit argument: " ++ show ai

              mergeNullTypes :: NullType -> NullType -> TcDeclM NullType
              mergeNullTypes nt1 nt2 = return (joinNT nt1 nt2)


mergeTypesMaps :: TypesMap -> TypesMap -> TcDeclM TypesMap
mergeTypesMaps = mergeGeneric mergeVarMaps

------------------------------------------
-- Policy tracking
------------------------------------------

mergePolicies :: PolicyMap -> PolicyMap -> TcDeclM PolicyMap
mergePolicies = mergeGeneric mergePs

mergePs :: PolicyInfo -> PolicyInfo -> TcDeclM PolicyInfo
mergePs pi1 pi2 =
    case (pBounds pi1, pBounds pi2) of
      (KnownPolicy p, KnownPolicy q)
          | p == q    -> return $ PI (pStable pi1) $ KnownPolicy p
          | otherwise -> mkBounds p q p q
      (PolicyBounds p1 p2, PolicyBounds q1 q2) -> mkBounds p1 q1 p2 q2
      (KnownPolicy  p,     PolicyBounds q1 q2) -> mkBounds p  q1 p  q2
      (PolicyBounds p1 p2, KnownPolicy  q    ) -> mkBounds p1 q  p2 q

  where mkBounds a b c d = PI (pStable pi1) <$>
                             (PolicyBounds <$> a `glb` b <*> c `lub` d)

------------------------------------------
-- Actor analysis
------------------------------------------
{-
scrambles :: Stability -> Stability -> Bool
scrambles FullV (FieldV _) = True
scrambles x y = x == y

scramble :: Stability -> CodeState -> BaseM CodeState
scramble stab state = do
    let acts = Map.toAscList $ actorSt state
    newActs <- mapM (\(k,v) -> scramble' stab v >>= \v' -> return (k, v')) acts
    return state { actorSt = Map.fromAscList newActs }

scramble' :: Stability -> ActorInfo -> BaseM ActorInfo
scramble' stab a@(AI _ stab') =
    if scrambles stab stab'
     then do aid' <- newUnknown
             return $ AI aid' stab'
     else return a

-}
{-
mergeActors :: ActorMap -> ActorMap -> BaseM ActorMap
mergeActors = mergeGeneric mergeActorInfo
  where mergeActorInfo :: ActorInfo -> ActorInfo -> BaseM ActorInfo
        mergeActorInfo ai1 ai2 | ai1 == ai2 = return ai1
        mergeActorInfo (AI st _) _ = do
          aid <- ConcreteActorId <$> newUnknown
          return $ AI st aid
-}
------------------------------------------
-- Exception states
------------------------------------------

type ExnsMap  = Map.Map ExnType ExnPoint
data ExnType  = ExnType TcType | ExnContinue | ExnBreak | ExnReturn
  deriving (Eq, Ord, Show, Data, Typeable)
data ExnPoint = ExnPoint { epState :: CodeState, epWrite :: ActorPolicy }
  deriving (Eq, Show, Data, Typeable)



mergeExns :: ExnsMap -> ExnsMap -> TcDeclM ExnsMap
mergeExns em1 em2 = do
    let newKeys = Map.keys em1 `union` Map.keys em2
        oldVals = map (\k -> (Map.lookup k em1, Map.lookup k em2)) newKeys
    newVals <-mapM (uncurry mergePoints) oldVals
    return $ Map.fromList $ zip newKeys newVals

-- Invariant: At most one of the two arguments can be Nothing
mergePoints :: Maybe ExnPoint -> Maybe ExnPoint -> TcDeclM ExnPoint
mergePoints Nothing (Just e) = return e
mergePoints (Just e) Nothing = return e
mergePoints (Just (ExnPoint st1 w1)) (Just (ExnPoint st2 w2)) = do
  st <- mergeStates st1 st2
  w <- w1 `lub` w2
  return (ExnPoint st w)
mergePoints _ _ = panic (codeStateModule ++ ".mergePoints")
                  "Both ExnPoint arguments cannot be missing!"

-- This should probably be pre-computed each time the map is updated instead
exnPC :: CodeState -> [(ActorPolicy, String)]
exnPC s = map (\(tyX,ptX) -> (epWrite ptX, errorSrc tyX)) $ Map.assocs $ exnS s

errorSrc :: ExnType -> String
errorSrc et = "area of influence of " ++
    case et of
      ExnBreak -> "a break statement"
      ExnContinue -> "a continue statement"
      ExnReturn -> "a return statement"
      ExnType tX -> "exception " ++ prettyPrint tX
