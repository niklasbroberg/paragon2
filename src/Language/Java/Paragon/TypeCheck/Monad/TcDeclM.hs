{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
             TupleSections,  BangPatterns #-}
module Language.Java.Paragon.TypeCheck.Monad.TcDeclM
    (
     module Language.Java.Paragon.Monad.PiReader,

     TcDeclM, runTcDeclM, TypeCheck,

     MonadTcDeclM(..), -- MonadTcBaseM(..),

     fetchPkg, fetchType, skolemTypeDecl,

     getThisType, getThisStateType, getSuperType,
     getTypeMap, lookupTypeOfType, lookupTypeOfStateType,
     getLocalTypeMap,

     withTypeParam, extendGlobalTypeMap,

     evalSrcType, evalSrcRefType, evalSrcClsType,
     evalSrcTypeArg, evalSrcNWTypeArg,
     evalReturnType,

     genBot, genMeta,

     EvalPolicyM(..),
     -- evalPolicy, -- evalPolicyExp,
     -- evalLock, -- evalActor,
     evalSrcLockProps, getLockModProps,

     freshActorId, unknownActorId, instanceActorId,
     newMetaPolVar,

     getReadPolicy, getWritePolicy, getLockPolicy,
     getParamPolicy, getReturnPolicy, getExnReadPolicy

    ) where

import Language.Java.Paragon.Monad.PiReader

import Language.Java.Paragon.Error
import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.NameResolution
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.TypeCheck.TypeMap
import Language.Java.Paragon.TypeCheck.Types
import qualified Language.Java.Paragon.PolicyLang as PL
import Language.Java.Paragon.TypeCheck.NullAnalysis
import Language.Java.Paragon.TypeCheck.Interpreter

import Control.Monad hiding (join)
import Control.Applicative

import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as B
import Data.List (partition, unzip4)
import Data.Maybe (catMaybes, mapMaybe, isJust, maybeToList)

import qualified Control.Monad.Fail as Fail

tcDeclMModule :: String
tcDeclMModule = typeCheckerBase ++ ".Monad.TcDeclM"

type TypeCheck m ast = ast SourcePos -> m (ast T)

lookupTypeOfStateType :: MonadTcDeclM m => TcStateType -> m TypeSig
lookupTypeOfStateType sty {-@(TcInstance{})-} = liftTcDeclM $ do
  tm <- getTypeMap
  case lookupTypeOfStateT sty tm of
    Right tsig -> return tsig
    Left Nothing -> fail $ "Unknown type: " ++ prettyPrint sty
    Left (Just err) -> fail err
{-
lookupTypeOfStateType _sty@(TcType ty) = liftTcDeclM $ do
  tm <- getTypeMap
  case lookupTypeOfT ty tm of
    Right (is, tsig) -> do
      ias <- mapM (instanceActorId . Name SourcePos EName
-}
lookupTypeOfType :: MonadTcDeclM m => TcType -> m ([(RefType SourcePos, B.ByteString)], TypeSig)
lookupTypeOfType ty = liftTcDeclM $ do
  tm <- getTypeMap
--  debugPrint $ "lookupTypeOfType -- TypeMap:\n" ++ prettyPrint tm
  case lookupTypeOfT ty tm of
    Right tsig -> return tsig
    Left Nothing -> fail $ "Unknown type: " ++ prettyPrint ty
    Left (Just err) -> fail err


fetchPkg :: Name SourcePos -> TcDeclM SourcePos
fetchPkg n@(Name pos _ _ _) = do
  debugPrint $ "Fetching package " ++ prettyPrint n ++ " ..."
  isP <- doesPkgExist n
  if not isP
   then fail $ "No such package: " ++ prettyPrint n
   else do
     extendGlobalTypeMap (extendTypeMapP n emptyTM)
     debugPrint $ "Done fetching package " ++ prettyPrint n
     return pos


fetchType :: Name SourcePos -> TcDeclM ([TypeParam SourcePos],[(RefType SourcePos, B.ByteString)],TypeSig)
fetchType n@(Name pos _ _ typName) = do
  withFreshCurrentTypeMap $ do
  debugPrint $ "Fetching type " ++ prettyPrint n ++ " ..."
  isT <- doesTypeExist n
  if not isT
   then fail $ "No such type: " ++ prettyPrint n
   else do
     cUnit <- getTypeContents n
     pp <- getPiPath
     CompilationUnit _ pkg _ [td] <- liftBase $ resolveNames pp cUnit
     withThisType (snd $ skolemTypeDecl td) $
      case td of
       ClassTypeDecl _ (ClassDecl _ ms cuName tps mSuper impls (ClassBody _ ds)) -> do
               check (typName == cuName) $
                 mkError (FileClassMismatchFetchType (prettyPrint typName) (prettyPrint cuName))
                         --(identPos cuName)
                         pos
               withFoldMap withTypeParam tps $ do
                 superTys <- --map (TcRefT . TcClsRefT) <$>
                              mapM (evalSrcClsType genBot) (maybeToList mSuper)
                 implsTys  <- --map (TcRefT . TcClsRefT) <$>
                              mapM (evalSrcClsType genBot) impls

                 -- Remove this line, and set tMembers to emptyTM,
                 -- if using "clever lookup" instead of "clever setup"
                 debugPrint $ "fetchType[superType]: " ++ prettyPrint superTys
                 superTm <- case superTys of
                              [] -> return emptyTM
                              [superTy] -> tMembers . snd <$>
                                           lookupTypeOfType (clsTypeToType superTy)
                              _ -> panic (tcDeclMModule ++ ".fetchType")
                                 $ "More than one super class for class:"  ++ show superTys
                 debugPrint $ "fetchType[superTm]:\n" ++ prettyPrint superTm

                 let tnam = Name pos TName (fmap (\(PackageDecl _ pn) -> pn) pkg) typName
                     tsig = TSig {
                              tType = TcClsRefT $ TcClassT tnam [],
                              tIsClass = True,
                              tIsFinal = Final pos `elem` ms,
                              tSupers  = superTys,
                              tImpls   = implsTys,
                              tMembers = superTm -- { constrs = Map.empty }
                            }
                     mDs = map unMemberDecl ds
                     iaps = findImplActorParams mDs
                 debugPrint $ "Adding for name: " ++ prettyPrint n
                 extendGlobalTypeMap (extendTypeMapT n tps iaps tsig)
                 when (isJust pkg) $
                      extendGlobalTypeMap (extendTypeMapT (mkSimpleName TName cuName) tps iaps tsig)

                 debugPrint "fetchType[pkg]"

--               (rtps,rsig) <- withTypeMapAlways (extendTypeMapT n tps tsig) $ do
--               withFoldMap withTypeParam tps $ do
                 fetchActors n mDs $ do

                 debugPrint "fetchType[fetchActors]"
                 let mDss = map (:[]) mDs
                 withFoldMap (fetchLTPs n) mDss $ do

--                 fetchLocks  n mDs $ do
--                 fetchPols   n mDs $ do
--                 fetchTypeMethods n mDs $ do
                 debugPrint "fetchType[fetchLTPs]"
                 fetchSignatures (Native pos `elem` ms) n mDs
                 debugPrint "fetchType[fetchSignatures]"

                 tm <- getTypeMap
                 debugPrint $ "fetchType[final TM]:\n" ++ prettyPrint tm
                 case lookupNamed types n tm of
                   Just res -> do
                     debugPrint $ "Done fetching type: " ++ prettyPrint n
--                     debugPrint $ "Result: " ++ show res ++ "\n"
                     return res
                   Nothing  -> panic (tcDeclMModule ++ ".fetchType") $
                               "Just fetched type " ++ show n ++
                              " but now it doesn't exist!"
--               withTypeMapAlways (extendTypeMapT n rtps rsig) $ do
--                 tm <- getTypeMap
--                 debugPrint $ "TypeMap here: " ++ show tm ++ "\n"
--                 return (rtps,rsig)

              where unMemberDecl :: Decl SourcePos -> MemberDecl SourcePos
                    unMemberDecl (MemberDecl _ md) = md
                    unMemberDecl _ = panic (tcDeclMModule ++ ".fetchType")
                                     "Malformed PI-file contains initializer block"
       InterfaceTypeDecl _ (InterfaceDecl _ ms cuName tps supers (InterfaceBody _ mDs)) -> do
               check (typName == cuName) $
                     toUndef $ "File name " ++ prettyPrint typName  ++ " does not match class name " ++ prettyPrint cuName
               superTys <- --map (TcRefT . TcClsRefT) <$>
                              mapM (evalSrcClsType genBot) supers

               -- Remove this line, and set tMembers to emptyTM,
               -- if using "clever lookup" instead of "clever setup"
               superTm <- foldl merge emptyTM <$>
                            mapM ((tMembers . snd <$>) . lookupTypeOfType . clsTypeToType) superTys

               let tnam = Name defaultPos TName (fmap (\(PackageDecl _ pn) -> pn) pkg) typName
                   tsig = TSig {
                            tType = TcClsRefT $ TcClassT tnam [],
                            tIsClass = False,
                            tIsFinal = Final defaultPos `elem` ms,
                            tSupers  = superTys,
                            tImpls   = [],
                            tMembers = superTm
                          }

               extendGlobalTypeMap (extendTypeMapT n tps [] tsig)
               when (isJust pkg) $
                    extendGlobalTypeMap (extendTypeMapT (mkSimpleName TName cuName) tps [] tsig)

--               withTypeMapAlways (extendTypeMapT n tps tsig) $ do
               withFoldMap withTypeParam tps $ do
                 -- These will be written directly into the right
                 -- places in the TM, using the 'always' trick
                 fetchActors n mDs $ do

                 let mDss = map (:[]) mDs
                 withFoldMap (fetchLTPs n) mDss $ do

--                 fetchLocks  n mDs $ do
--                 fetchPols   n mDs $ do
--                 fetchTypeMethods n mDs $ do

                 fetchSignatures (Native defaultPos `elem` ms) n mDs

                 tm <- getTypeMap
                 case lookupNamed types n tm of
                   Just res -> return res
                   Nothing  -> panic (tcDeclMModule ++ ".fetchType") $
                               "Just fetched type " ++ show n ++
                               " but now it doesn't exist!"

       _ -> fail "Enums not yet supported"

fetchType n = panic (tcDeclMModule ++ ".fetchType") $ show n

fetchLTPs :: Name SourcePos -> [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
fetchLTPs n mDs tdma = do
            fetchLocks  n mDs $ do
            fetchPols   n mDs $ do
            fetchTypeMethods n mDs tdma



findImplActorParams :: [MemberDecl SourcePos] -> [(RefType SourcePos, B.ByteString)]
findImplActorParams mds = [ (rt, unIdent i)
                                | FieldDecl _ ms (RefType _ rt) vds <- mds,
                                  Final defaultPos `elem` ms, Static defaultPos `notElem` ms,
                                  VarDecl _ (VarId _ i) Nothing <- vds ]

-- Actors

fetchActors :: Name SourcePos -> [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
fetchActors n mDecls tdra = do
    -- debugPrint $  "fetchActors: " ++ show
    let acts = [ (ms, rt, vd)
                     | FieldDecl _ ms (RefType _ rt) vds <- mDecls
                     , vd <- vds
                     , Final defaultPos `elem` ms -- Static defaultPos `elem` ms
               ]
--    let -- (sfs,unstables)  = partition (\(ms, _) -> Final defaultPos `elem` ms) acts
--        (spawns  , stables ) = partition (\(_,_,VarDecl _ _ initz) -> initz == Nothing) acts -- sfs
--        (sspawns , fspawns ) = partition (\(ms,_,_) -> Static defaultPos `elem` ms) spawns
--        (sstables, fstables) = partition (\(ms,_,_) -> Static defaultPos `elem` ms) stables

--    (ssas, ssvs) <- unzip <$> mapM spawnActorVd sspawns
--    (fsas, fsvs) <- unzip <$> mapM paramActorVd fspawns
--    (seas, sevs) <- unzip <$> mapM evalActorVd  sstables
--    (feas, fevs) <- unzip <$> mapM evalActorVd  fstables
--    (aas, avs) <- unzip <$> mapM unknownActorVd unstables
--    (eas, evs) <- unzip <$> mapM evalActorVd stables
    eas <- mapM evalActorVd acts
    let globTM = emptyTM { actors = Map.fromList eas }
--                           fields = Map.fromList (ssvs ++ fsvs ++ sevs ++ fevs) }
        loclTM = emptyTM { actors = Map.fromList eas }
--                           fields = Map.fromList (ssvs ++ fsvs ++ sevs ++ fevs) }

    extendGlobalTypeMap (extendTypeMapN n $ merge globTM)
    withCurrentTypeMap (return . merge loclTM) $ do
--      debugPrint "Actors fetched"
      tdra


         where evalActorVd {-, spawnActorVd, paramActorVd , unknownActorVd -}
                   :: ([Modifier SourcePos], RefType SourcePos, VarDecl SourcePos)
                   -> TcDeclM (B.ByteString, PL.TypedActorIdSpec)
                  -- Static, only Nothing for initializer
{-               spawnActorVd (ms, rt, VarDecl _ (VarId _ i) _) = do
                 rTy <- evalSrcRefType genBot rt
                 a <- PL.TypedActorIdSpec rTy . PL.ConcreteActorId <$> freshActorId (prettyPrint i)
                 p <- PL.VarPolicy <$> getReadPolicy ms
                 let vti = VSig (TcRefT rTy) p False
                            (Static defaultPos `elem` ms) (Final defaultPos `elem` ms) False
                 return ((unIdent i,a),(unIdent i,vti))
               spawnActorVd (_, _, VarDecl _ arvid _) =
                   fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

               paramActorVd (ms, rt, VarDecl _ (VarId _ i) _) = do
                 rTy <- evalSrcRefType genBot rt
                 let a = PL.TypedActorIdSpec rTy $ PL.ActorTPVar $ unIdent i
                 p <- PL.VarPolicy <$> getReadPolicy ms
                 let vti = VSig (TcRefT rTy) p False
                           (Static defaultPos `elem` ms) (Final defaultPos `elem` ms) False
                 return ((unIdent i,a),(unIdent i,vti))
               paramActorVd (_, _, VarDecl _ arvid _) =
                   fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

               -- All non-final
               unknownActorVd (ms, VarDecl _ (VarId _ i) _) = do
                 p <- getReadPolicy ms
                 let vti = VSig actorT p False (Static defaultPos `elem` ms) (Final defaultPos `elem` ms)
                 a <- unknownActorId
                 return ((i,a),(i,vti))

               unknownActorVd (_, VarDecl _ arvid _) =
                   fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid
 -}
               -- Final --, with explicit initializer
               evalActorVd (ms, rt, VarDecl _ (VarId _ i) mInit) = do
                 rTy <- evalSrcRefType genBot rt
--                 p <- PL.VarPolicy <$> getReadPolicy ms
--                 let vti = VSig (TcRefT rTy) p False
--                           (Static defaultPos `elem` ms) (Final defaultPos `elem` ms) False
                 a <- case mInit of
                        Just (InitExp _ e) -> do
                          case e of
                            ExpName _ nam -> do
                               tm <- getTypeMap
                               case lookupNamed actors nam tm of
                                 Just a -> return a
                                 Nothing -> PL.TypedActorIdSpec rTy . PL.ConcreteActorId <$> unknownActorId --fail "Internal error: no such actor"
                            InstanceCreation{} -> do
                                 PL.TypedActorIdSpec rTy .
                                   PL.ConcreteActorId <$> freshActorId (B.unpack $ unIdent i)
                            _ -> PL.TypedActorIdSpec rTy .
                                      PL.ConcreteActorId <$> unknownActorId
                        Nothing -> PL.TypedActorIdSpec rTy .
                                       PL.ConcreteActorId <$> unknownActorId
                 debugPrint $ "Evaluated field \"" ++ prettyPrint i ++ "\" to have actor id: " ++ prettyPrint a
                 return (unIdent i,a)

--               evalActorVd (_, _, VarDecl _ _ Nothing)
--                   = panic (typeCheckerBase ++ ".evalActorVd") $ "No initializer"
               evalActorVd (_, _, VarDecl _ arvid _)
                   = fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

-- end actors

-- locks

fetchLocks :: Name SourcePos -> [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
fetchLocks n mds tdra = do
  let lcs = [ (i, ms, tys, mProps) |
               LockDecl _ ms i tys mProps <- mds ]
  unless (null lcs) $ debugPrint $ "fetchLocks: " ++ show lcs
  lsigs <- forM lcs $ \(i, ms, tys, mProps) -> do
                     pol <- getLockPolicy ms
                     rTys <- mapM (evalSrcRefType genBot) tys
                     modPrs <- getLockModProps (Just n) i ms
                     prs <- evalSrcLockProps i mProps
                     return (unIdent i, LSig (PL.VarPolicy pol) rTys (modPrs ++ prs))
  let newTM = emptyTM { locks = Map.fromList lsigs }
  extendGlobalTypeMap (extendTypeMapN n $ merge newTM)
  withCurrentTypeMap (return . merge newTM) $ do
--       debugPrint $ "Locks fetched"
       tdra

getLockModProps :: Maybe (Name SourcePos) -> Ident SourcePos
                -> [Modifier SourcePos] -> TcDeclM PL.GlobalPol
getLockModProps mTypN lockI ms = do
    let lockN = Name (ann lockI) LName mTypN lockI -- mkSimpleName LName lockI
        [domX,domY,domZ]  = map (anyActor . B.singleton) "xyz"
        [varX,varY,varZ] = map PL.QuantActor [0,1,2]
        atom n = PL.AtomPred . PL.Atom n
        trans = PL.DatalogClause [domX,domY,domZ]
                    (atom lockN [varX, varY])
                         [atom lockN [varX, varZ], atom lockN [varZ, varY]]
        refl  = PL.DatalogClause [domX] (atom lockN [varX, varX]) []
        symm  = PL.DatalogClause [domX,domY]
                    (atom lockN [varX, varY]) [atom lockN [varY, varX]]
    return $
       [ trans | Transitive _ <- ms ] ++
       [ refl  | Reflexive  _ <- ms ] ++
       [ symm  | Symmetric  _ <- ms ]


anyActor :: B.ByteString -> PL.ActorSetRep
anyActor b = PL.TypedActor (TcClsRefT objectT) b

-- end locks

-- policies

fetchPols :: Name SourcePos -> [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
fetchPols n mds tdra = do
  let pols = [ (unIdent i,initz, Static defaultPos `elem` ms) |
                 FieldDecl _ ms (PrimType _ (PolicyT _)) vds <- mds,
                 VarDecl _ (VarId _ i) (Just (InitExp _ initz)) <- vds,
                 Final defaultPos `elem` ms
             ]
      (spols, fpols) = partition (\(_,_,b) -> b) pols

  unless (null pols) $ do
                         debugPrint "fetchPols: "
                         mapM_ (debugPrint . ("  " ++) . show) pols
  sips <- mapM fetchPol spols
  fips <- mapM fetchPol fpols

  -- TODO: Expand local locks!
  let globTM = emptyTM { policies = Map.fromList sips }
      loclTM = emptyTM { policies = Map.fromList $ sips ++ fips }
  extendGlobalTypeMap $ extendTypeMapN n $ merge globTM
  withCurrentTypeMap (return . merge loclTM) $ do
--  withTypeMapAlways (extendTypeMapN n (merge $ emptyTM { policies = Map.fromList ips })) $ do
--                    debugPrint $ "Policies fetched"
                    tdra

      where fetchPol :: (B.ByteString, Exp SourcePos, a)
                     -> TcDeclM (B.ByteString, PL.PrgPolicy)
            fetchPol (i,e,_) = (i,) <$> evalPolicy e
-- end policies

-- Working with typemethods
fetchTypeMethods ::  Name SourcePos -> [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
fetchTypeMethods n mds tdra = do
  let ipbs = [ (unIdent i,(ps,body)) |
               MethodDecl _ ms _ _ i ps _ (MethodBody _ (Just body)) <- mds,
               Typemethod defaultPos `elem` ms
             ]
  ipidbs <- mapM paramsToIdents ipbs
  let newTM = emptyTM { typemethods = Map.fromList ipidbs }
  extendGlobalTypeMap $ extendTypeMapN n $ merge newTM
  withCurrentTypeMap (return . merge newTM) $ do
--  withTypeMapAlways (extendTypeMapN n
--                     (merge $ emptyTM { typemethods = Map.fromList ipidbs })) $ do
--                    debugPrint "TypeMethods fetched"
                    tdra

    where paramsToIdents (i, (ps,b)) = do
                              pids <- mapM paramIdent ps
                              return (i, (pids,b))
          paramIdent :: FormalParam SourcePos -> TcDeclM B.ByteString
          paramIdent (FormalParam _ _ _ _ (VarId _ i)) = return $ unIdent i
          paramIdent (FormalParam _ _ _ _ arvid) =
              fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

-- end typemethods

-- signatures of fields, methods and constructors

fetchSignatures :: Bool -> Name SourcePos -> [MemberDecl SourcePos] -> TcDeclM ()
fetchSignatures isNative n memDs = do
    fieldMap <- fetchFields memDs
    methodMap <- fetchMethods memDs
    constrMap <- fetchConstrs memDs
    let newTM = emptyTM
                { fields = fieldMap,
                  methods = methodMap,
                  constrs = constrMap }
    extendGlobalTypeMap $ extendTypeMapN n $ merge newTM
--    debugPrint "Signatures fetched"
    return ()

 where
   unVarDecl :: VarDecl SourcePos -> TcDeclM B.ByteString
   unVarDecl (VarDecl _ (VarId _ i) _) = return $ unIdent i
   unVarDecl arvid = fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

   fetchFields :: [MemberDecl SourcePos] -> TcDeclM (Map B.ByteString VarFieldSig)
   fetchFields = go Map.empty
       where go :: Map B.ByteString VarFieldSig
                -> [MemberDecl SourcePos]
                -> TcDeclM (Map B.ByteString VarFieldSig)
             go acc [] = return acc
             go fm (md:mds) =
                 case md of
                   FieldDecl _ ms ty vds -> do
                      tcty <- evalSrcType genBot ty
                      pol  <- getReadPolicy ms
                      let vti = VSig tcty (PL.VarPolicy pol)
                                  False (Static defaultPos `elem` ms) (Final defaultPos `elem` ms) (Notnull defaultPos `elem` ms)
                      ids <- mapM unVarDecl vds
                      let newFm = foldl (\m i -> Map.insert i vti m) fm ids
                      go newFm mds
                   _ -> go fm mds

   fetchMethods :: [MemberDecl SourcePos]
                -> TcDeclM (Map B.ByteString MethodMap)
   fetchMethods = go Map.empty
       where go :: Map B.ByteString MethodMap
                -> [MemberDecl SourcePos]
                -> TcDeclM (Map B.ByteString MethodMap)
             go acc [] = return acc
             go mm (md:mds) =
                 case md of
                   MethodDecl _ ms tps retT i ps exns _ -> do
                           withFoldMap withTypeParam tps $ do
                             tcty <- evalReturnType genBot retT
                             (pTys, pIs, pPols, mnnp) <- unzip4 <$> mapM paramInfo ps
                             rPol <- getReturnPolicy ms pPols
                             wPol <- getWritePolicy ms
                             exs <- mapM eSpecToSig exns
                             expects <- mapM evalLock $ concat [ l | Expects _ l <- ms ]
                             closes  <- map PL.skolemizeLock <$>
                                          (mapM evalLock $ concat [ l | Closes  _ l <- ms ])
                             opens   <- map PL.skolemizeLock <$>
                                          (mapM evalLock $ concat [ l | Opens   _ l <- ms ])
                             let nnp = [x | (Just x) <- mnnp]
                             let mti = MSig {
                                         mRetType   = tcty,
                                         mModifiers = removeAnnotationMany ms,
                                         mRetPol    = PL.VarPolicy rPol,
                                         mPars      = pIs,
                                         mParBounds = map PL.VarPolicy pPols,
                                         mWrites    = PL.VarPolicy wPol,
                                         mExpects   = expects,
                                         mLMods     = PL.LockDelta opens closes,
                                         mExns      = exs,
                                         mNNPars    = nnp,
                                         mIsNative  = isNative
                                       }
                                 isVarArity = case reverse ps of
                                                [] -> False
                                                (FormalParam _ _ _ b _ : _) -> b
                                 newMethMap = Map.singleton (tps, pTys, isVarArity) mti
                                 newMm = Map.insertWith Map.union (unIdent i) newMethMap mm
                             go newMm mds

                   _ -> go mm mds

   fetchConstrs = go Map.empty
       where go :: ConstrMap
                -> [MemberDecl SourcePos]
                -> TcDeclM ConstrMap
             go acc [] = return acc
             go cm (md:mds) =
                 case md of
                   ConstructorDecl _ ms tps _ ps exns _ -> do
                           withFoldMap withTypeParam tps $ do
                             (pTys, pIs, pPols, pMnn) <- unzip4 <$> mapM paramInfo ps
                             wPol <- getWritePolicy ms
                             exs <- mapM eSpecToSig exns
                             expects <- mapM evalLock $ concat [ l | Expects _ l <- ms ]
                             closes  <- map PL.skolemizeLock <$>
                                          (mapM evalLock $ concat [ l | Closes  _ l <- ms ])
                             opens   <- map PL.skolemizeLock <$>
                                          (mapM evalLock $ concat [ l | Opens   _ l <- ms ])
                             let pnn = [x | (Just x) <- pMnn]
                             let cti = CSig {
                                         cPars      = pIs,
                                         cParBounds = map PL.VarPolicy pPols,
                                         cWrites    = PL.VarPolicy wPol,
                                         cExpects   = expects,
                                         cLMods     = PL.LockDelta opens closes,
                                         cExns      = exs,
                                         cNNPars    = pnn,
                                         cIsNative  = isNative
                                       }
                                 isVarArity = case reverse ps of
                                                [] -> False
                                                (FormalParam _ _ _ b _ : _) -> b
                                 newCm = Map.insert (tps, pTys, isVarArity) cti cm
                             go newCm mds

                   _ -> go cm mds


   eSpecToSig :: ExceptionSpec SourcePos -> TcDeclM (TcType, ExnSig)
   eSpecToSig (ExceptionSpec _ ms eType) = do
          ty <- evalSrcType genBot (RefType defaultPos eType) -- should use evalSrcRefType
          rPol <- getReadPolicy ms
          wPol <- getWritePolicy ms
          opens  <- mapM evalLock $ concat [ l | Opens  _ l <- ms ]
          closes <- mapM evalLock $ concat [ l | Closes _ l <- ms ]
          let esig = ExnSig {
                       exnReads = PL.VarPolicy rPol,
                       exnWrites = PL.VarPolicy wPol,
                       exnMods = PL.LockDelta
                                   (map PL.skolemizeLock opens)
                                   (map PL.skolemizeLock closes)
                     }
          return (ty, esig)

   paramInfo :: FormalParam SourcePos -> TcDeclM (TcType, B.ByteString, PL.PrgPolicy, Maybe B.ByteString)
   paramInfo (FormalParam _ ms ty _ (VarId _ i)) = do
          pPol <- getParamPolicy (unIdent i) ms
          pTy  <- evalSrcType genBot ty
          let mNn = if Notnull defaultPos `elem` ms then Just $ unIdent i else Nothing
          return (pTy, unIdent i, pPol, mNn)
   paramInfo (FormalParam _ _ _ _ arvid) =
            fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

withTypeParam :: TypeParam SourcePos -> TcDeclM a -> TcDeclM a
withTypeParam tp tcba =
    case tp of
      ActorParam _ rt i -> do
          topp <- PL.topM
          rTy <- evalSrcRefType genBot rt
          let vti = VSig (TcRefT rTy) topp False False True False
              bI  = unIdent i
          withCurrentTypeMap (\tm ->
              return $ tm { actors = Map.insert bI (PL.TypedActorIdSpec rTy $ PL.ActorTPVar bI) (actors tm),
                            fields = Map.insert bI vti (fields tm) }) $ tcba
      PolicyParam _ i -> do
           topp <- PL.topM
           let vti = VSig policyT topp False False True False
               bI  = unIdent i
           withCurrentTypeMap (\tm ->
              return $ tm { policies = Map.insert bI (PL.PolicyVar $ PL.PolicyTypeParam bI) (policies tm),
                            fields   = Map.insert bI vti (fields tm) }) $ tcba
      LockStateParam _ i -> do
          topp <- PL.topM
          let lti = LSig topp [] []
          withCurrentTypeMap (\tm ->
              return $ tm { locks = Map.insert (unIdent i) lti (locks tm) }) $ tcba
      TypeParam _ _i _ -> do
          --withCurrentTypeMap (\tm ->
          --    tm { types = Map.insert i ([],Map.empty) (types tm) }) $
            tcba


{-
fetchSignature :: MemberDecl () -> TcDeclM a -> TcDeclM a
fetchSignature memDecl tcba = do

    --debug $ "fetchSignature: " ++ show memberDecl
    case memDecl of
      FieldDecl _ ms ty vds -> do
        tcty <- evalSrcType ty
        pol  <- getReadPolicy ms
        let vti = VSig tcty pol False (Static defaultPos `elem` ms) (Final defaultPos `elem` ms)
        ids <- mapM unVarDecl vds
        withTypeMap (\tm ->
           tm { fields = foldl
                         (\m i -> Map.insert i vti m)
                         (fields tm) ids
              }) $
          tcba
      MethodDecl _ ms tps retT i ps exns _ -> do
        withFoldMap withTypeParam tps $ do
        tcty <- evalReturnType retT
        (pTys, pPols) <- unzip <$> mapM paramInfo ps
        rPol <- getReturnPolicy ms pPols
        wPol <- getWritePolicy ms
        exs <- mapM eSpecToSig exns
        expects <- mapM evalLock $ concat [ l | Expects _ l <- ms ]
        closes  <- mapM evalLock $ concat [ l | Closes  _ l <- ms ]
        opens   <- mapM evalLock $ concat [ l | Opens   _ l <- ms ]
        let mti = MSig {
                      mRetType = tcty,
                      mRetPol  = rPol,
                      mPars    = pPols,
                      mWrites  = wPol,
                      mExpects = expects,
                      mLMods   = (closes, opens),
                      mExns    = exs
                    }
        withTypeMap (\tm ->
          tm { methods = Map.insert (i, pTys) (tps,mti) (methods tm) }) $
            tcba
      ConstructorDecl _ ms tps _ ps exns _ -> do
        withFoldMap withTypeParam tps $ do
        (pTys, pPols) <- unzip <$> mapM paramInfo ps
        wPol <- getWritePolicy ms
        exs <- mapM eSpecToSig exns
        expects <- mapM evalLock $ concat [ l | Expects _ l <- ms ]
        closes  <- mapM evalLock $ concat [ l | Closes  _ l <- ms ]
        opens   <- mapM evalLock $ concat [ l | Opens   _ l <- ms ]
        let cti = CSig {
                      cPars    = pPols,
                      cWrites  = wPol,
                      cExpects = expects,
                      cLMods   = (closes, opens),
                      cExns    = exs
                    }
        withTypeMap (\tm ->
          tm { constrs = Map.insert pTys (tps,cti) (constrs tm) }) $
            tcba
      LockDecl _ ms i mps Nothing -> do
        pL <- getLockPolicy ms
        -- TODO: Store lock properties!
        let lsig = LSig pL (length mps)
        withTypeMap (\tm ->
          tm { locks = Map.insert i lsig (locks tm) }) $
            tcba
      LockDecl {} -> fail "Lock properties not yet supported"
      _ -> fail "Inner classes not yet supported"

  where eSpecToSig :: ExceptionSpec SourcePos -> TcDeclM (TcType, ExnSig)
        eSpecToSig (ExceptionSpec _ ms eType) = do
          ty <- evalSrcType (RefType () eType) -- should use evalSrcRefType
          rPol <- getReadPolicy ms
          wPol <- getWritePolicy ms
          opens  <- mapM evalLock $ concat [ l | Opens  _ l <- ms ]
          closes <- mapM evalLock $ concat [ l | Closes _ l <- ms ]
          let esig = ExnSig {
                       exnReads = rPol,
                       exnWrites = wPol,
                       exnMods = (closes, opens)
                     }
          return (ty, esig)

        paramInfo :: FormalParam SourcePos -> TcDeclM (TcType, TcPolicy)
        paramInfo (FormalParam _ ms ty _ (VarId _ i)) = do
          pPol <- getParamPolicy i ms
          pTy  <- evalSrcType ty
          return (pTy, pPol)
        paramInfo (FormalParam _ _ _ _ arvid) =
            fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid
-}



------------------------------------------------------------

-------------------------------------------------------------------------------------
getReadPolicy, getWritePolicy, getLockPolicy
    :: [Modifier SourcePos] -> TcDeclM PL.PrgPolicy
getReadPolicy mods =
    case [pol |Reads _ pol <- mods ] of -- !!0 -- Read Policy? what if no read policy?
      [pol] -> evalPolicy pol
      [] -> PL.bottomM
      _ -> fail "At most one read modifier allowed per field"

getWritePolicy mods =
    case [pol | Writes _ pol <- mods] of
      [pol] -> evalPolicy pol
      [] -> PL.topM
      _ -> fail "At most one write modifier allowed per method"

getLockPolicy mods =
    case [pol | Reads _ pol <- mods] of
      [pol] -> evalPolicy pol
      [] -> PL.topM
      _ -> fail "At most one read modifier allowed per lock"

getExnReadPolicy :: PL.ActorPolicy -> [Modifier SourcePos] -> TcDeclM PL.ActorPolicy
getExnReadPolicy def mods =
    case [pol | Reads _ pol <- mods ] of
      [pol] -> PL.VarPolicy <$> evalPolicy pol
      [] -> return def
      _  -> fail "At most one read modifier allowed per exception"

getParamPolicy :: B.ByteString -> [Modifier SourcePos] -> TcDeclM PL.PrgPolicy
getParamPolicy _i mods =
    case [pol | Reads _ pol <- mods ] of
       [pol] -> evalPolicy pol
       [] -> return $ PL.PolicyVar $ PL.PolicyOfVar _i -- IF GENERIC: top
       _ -> fail "At most one read modifier allowed per parameter"



getReturnPolicy :: [Modifier SourcePos] -> [PL.PrgPolicy] -> TcDeclM PL.PrgPolicy
getReturnPolicy mods pPols =
    case [pol | Reads _ pol <- mods ] of
      [pol] -> evalPolicy pol
      [] -> PL.bottomM >>= \bt -> foldM PL.lub bt pPols
      _ -> fail "At most one return modifier allowed per method"

-------------------------------------------------------------------
-- Evaluating types

class (HasSubTyping m, MonadTcDeclM m) => EvalPolicyM m where
  evalPolicy :: Exp SourcePos -> m PL.PrgPolicy
  evalActorId :: Name SourcePos -> m PL.TypedActorIdSpec
  evalActor :: [(Ident SourcePos, TcRefType)] -> Actor SourcePos -> m PL.ActorSetRep
  evalLock :: Lock SourcePos -> m PL.TcLock

instance HasSubTyping TcDeclM where
 --subTypeOf :: TcRefType -> TcRefType -> TcDeclM Bool
 subTypeOf TcNullT _ = return True
 subTypeOf rt1 rt2 | rt1 == rt2 = return True
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
                            _ -> panic (tcDeclMModule ++ ".subTypeOf")
                                 $ show rt

                    Left err -> panic (tcDeclMModule ++ ".subTypeOf")
                                $ "Looking up type:" ++ show rt ++ "\nError: " ++ show err
                    Right (_,tsig) -> return tsig
          let sups  = tSupers tsig
              impls = tImpls tsig
              allS  = map TcClsRefT $ sups ++ impls
          supsups <- mapM superTypes allS
          return $ concat $ allS:supsups



instance EvalPolicyM TcDeclM where
  evalPolicy = evalPolicyD
  evalActorId = evalActorIdD
  evalActor = evalActorD
  evalLock = evalLockD

evalReturnType :: EvalPolicyM m => m PL.ActorPolicy -> ReturnType SourcePos -> m TcType
evalReturnType _ (VoidType _) = return voidT
evalReturnType _ (LockType _) =
    fail "lock as return type not yet implemented" -- return TcLockRetT
evalReturnType gp (Type _ t)   = evalSrcType gp t

evalSrcType :: EvalPolicyM m => m PL.ActorPolicy -> Type SourcePos -> m TcType
evalSrcType _ (PrimType _ pt) = return $ TcPrimT pt
evalSrcType gp (RefType  _ rt) = TcRefT <$> evalSrcRefType gp rt
evalSrcType _ _ = panic (tcDeclMModule ++ ".evalSrcType")
                  "AntiQType should not appear in AST being type-checked"

evalSrcRefType :: EvalPolicyM m => m PL.ActorPolicy -> RefType SourcePos -> m TcRefType
evalSrcRefType _ (TypeVariable _ i) = return $ TcTypeVar $ unIdent i
evalSrcRefType genPol (ArrayType _ t mps) = do
  ty <- evalSrcType genPol t
  pols <- mapM (maybe genPol (\p -> PL.VarPolicy <$> evalPolicy p)) mps
  let (TcRefT arrTy) = mkArrayType ty pols
  return arrTy
evalSrcRefType gp (ClassRefType _ ct) = TcClsRefT <$> evalSrcClsType gp ct

evalSrcClsType :: EvalPolicyM m => m PL.ActorPolicy -> ClassType SourcePos -> m TcClassType
evalSrcClsType gp _ct@(ClassType _ n tas) = do
--  debugPrint $ "Evaluating class type: " ++ show _ct
  baseTm <- getTypeMap
  -- debugPrint $ "Current type map: " ++ show baseTm
  (tps,_iaps,_tsig) <- case lookupNamed types n baseTm of
                         Nothing -> liftTcDeclM $ fetchType n
                                    -- fail $ "Unknown type: " ++ prettyPrint n
                         Just res -> return res

--  debugPrint $ "Type found"
  tArgs <- zipWithM (evalSrcTypeArg gp) tps tas
--  debugPrint "Type arguments evaluated"
  return $ TcClassT n tArgs


evalSrcTypeArg :: EvalPolicyM m =>
                  m PL.ActorPolicy -> TypeParam SourcePos -> TypeArgument SourcePos -> m TcTypeArg
evalSrcTypeArg gp tp (ActualArg _ a) = evalSrcNWTypeArg gp tp a
evalSrcTypeArg _ _ _ = fail "evalSrcTypeArg: Wildcards not yet supported"

evalSrcNWTypeArg :: EvalPolicyM m =>
                    m PL.ActorPolicy -> TypeParam SourcePos -> NonWildTypeArgument SourcePos -> m TcTypeArg
-- Types may be names or types -- TODO: Check bounds
evalSrcNWTypeArg gp TypeParam{} (ActualName _ n) = do
    TcActualType . TcClsRefT <$> evalSrcClsType gp (ClassType defaultPos n [])
evalSrcNWTypeArg gp TypeParam{} (ActualType _ rt) =
    TcActualType <$> evalSrcRefType gp rt
-- Actors may only be names -- TODO: must be final
evalSrcNWTypeArg _ ActorParam{} (ActualName _ n) = TcActualActor <$> evalActorId n
-- Policies may be names, or special expressions -- TODO: names must be final
evalSrcNWTypeArg _ PolicyParam{} (ActualName _ n) =
    TcActualPolicy . PL.VarPolicy <$> evalPolicy (ExpName defaultPos n)
evalSrcNWTypeArg _ PolicyParam{} (ActualExp  _ e) =
    TcActualPolicy . PL.VarPolicy <$> evalPolicy e
-- Lock states must be locks
evalSrcNWTypeArg _ LockStateParam{} (ActualLockState _ ls) =
    TcActualLockState <$> mapM evalLock ls

evalSrcNWTypeArg _ tp nwta =
    fail $ "Trying to instantiate type parameter " ++ prettyPrint tp ++
           " with incompatible type argument " ++ prettyPrint nwta

{-
evalSrcNWTypeArg (ActualType   _ rt) = TcActualType <$> evalSrcRefType rt
evalSrcNWTypeArg (ActualPolicy _ p)  = TcActualPolicy <$> evalPolicy p
evalSrcNWTypeArg (ActualActor  _ n)  = TcActualActor <$> evalActorId n
evalSrcNWTypeArg (ActualLockState _ ls) = TcActualLockState <$> mapM evalLock ls
-}

evalPolicyD :: Exp SourcePos -> TcDeclM PL.PrgPolicy
evalPolicyD = interpretPolicy lookupFieldD

evalActorD :: [(Ident SourcePos, TcRefType)] -> Actor SourcePos -> TcDeclM PL.ActorSetRep
evalActorD = interpretActor lookupFieldD

evalActorIdD :: Name SourcePos -> TcDeclM PL.TypedActorIdSpec
evalActorIdD = interpretActorId lookupFieldD

{-
evalPolicy e = case e of
  ExpName _ n -> do
    debugPrint $ "evalPolicy: " ++ show n
    tm <- getTypeMap
    case lookupNamed policies n tm of
      Just p -> return p
      Nothing -> do
        case n of
          Name _ _ (Just tn@(Name _ TName _ _)) _ -> do
            _ <- fetchType tn
            evalPolicy e
          _ -> do
            debugPrint $ "Name causing problem: " ++ show n
            fail $ "evalPolicy: no such policy: " ++ prettyPrint n
  PolicyExp _ pl -> evalPolicyExp pl
  BinOp _ p1 (Add _) p2 -> do
    pol1 <- evalPolicy p1
    pol2 <- evalPolicy p2
    return $ pol1 `meet` pol2
  BinOp _ p1 (Mult _) p2 -> do
    pol1 <- evalPolicy p1
    pol2 <- evalPolicy p2
    return $ pol1 `join` pol2
  Paren _ p -> evalPolicy p
  MethodInv _ mi -> evalPolicyMethodInv mi
  _ -> fail ("evalPolicy: Not handled:\n" ++ (show e))

evalPolicyMethodInv :: MethodInvocation () -> TcDeclM (PrgPolicy TcActor)
evalPolicyMethodInv mi = do
  ap <- evalTypeMethod mi
  case ap of
    RealPolicy p -> return p
    _ -> panic (tcDeclMModule ++ ".evalPolicyMethodInv") $
         "Returned policy includes meta-variable: " ++ show ap

evalPolicyExp :: PolicyExp () -> TcDeclM (PrgPolicy TcActor)
evalPolicyExp (PolicyLit _ cs) = TcPolicy <$> mapM evalClause cs
evalPolicyExp (PolicyOf _ i)   = return $ TcRigidVar True (unIdent i)
evalPolicyExp (PolicyThis _)   = return $ TcThis
evalPolicyExp (PolicyTypeVar _ i) = return $ TcRigidVar False (unIdent i)

evalClause :: Clause () -> TcDeclM (TcClause TcActor)
evalClause (Clause _ h b) = do
  h' <- evalActor h
  b' <- mapM evalAtom b
  return $ TcClause h' b'

evalActorName :: ActorName () -> TcDeclM ActorId
evalActorName (ActorName _ n) = evalActorId n
evalActorName (ActorTypeVar _ i) = return $ ActorTPVar $ unIdent i

evalActor :: Actor () -> TcDeclM TcActor
evalActor (Actor _ n) = TcActor <$> evalActorName n
evalActor (Var _ i) = return $ TcVar (unIdent i)

evalActorId :: Name () -> TcDeclM ActorId
evalActorId n = do
  tm <- getTypeMap
  debugPrint $ "Evaluating actor id: " ++ prettyPrint n
  case lookupNamed actors n tm of
    Just aid -> do
      debugPrint $ "Actor id found: " ++ prettyPrint aid
      return aid
    Nothing -> do
      case n of
        Name _ _ (Just tn@(Name _ TName _ _)) _ -> do
            _ <- fetchType tn
            evalActorId n
        _ -> do
          debugPrint $ "Name causing problem: " ++ show n
          fail $ "evalActor: no such policy: " ++ prettyPrint n
  -- unknownActorId -- fail $ "evalActor: No such actor: " ++ prettyPrint n

evalAtom (Atom _ n as) = TcAtom n <$> mapM evalActor as
-}
evalAtom :: [(Actor SourcePos, PL.ActorRep)] -> Atom SourcePos -> PL.TcAtom
evalAtom = generalizeAtom

evalLockD :: Lock SourcePos -> TcDeclM PL.TcLock
evalLockD (Lock _ n@(Name _ _nt mPre i) ans) = do
  tm <- case mPre of
          Nothing -> getTypeMap
          Just pre -> do
              let preT = ClassType defaultPos pre []
              preTy <- evalSrcClsType PL.bottomM preT
              tm <- getTypeMap
              case lookupTypeOfT (clsTypeToType preTy) tm of
                Left Nothing -> panic (tcDeclMModule ++ ".evalLock")
                                $ "Just evaluated class type " ++ prettyPrint pre ++
                                  " but now it doesn't exist!"
                Left (Just err) -> panic (tcDeclMModule ++ ".evalLock")
                                   err
                Right (_, tsig) -> return $ tMembers tsig

  aids <- mapM getActor ans
  -- TODO: Here we need to get the types of all the TypedActorIdSpecs
  let rTysAids = map PL.actorType aids
  case Map.lookup (unIdent i) $ locks tm of
    Just lsig -> do
      mapM_ (\(rTy, rTyAid) ->
                 checkM (rTyAid `subTypeOf` rTy) $
                        toUndef $ "Lock " ++ prettyPrint n ++ " expects argument of type " ++
                                prettyPrint rTy ++ " but has been given argument of type " ++
                                prettyPrint rTyAid) $ zip (lArgs lsig) rTysAids
    Nothing -> fail $ "No such lock: " ++ prettyPrint n
  return $ PL.ConcreteLock $ PL.Lock n aids
evalLockD (LockVar _ i) = return $ PL.LockTypeParam $ unIdent i
evalLockD l = panic (tcDeclMModule ++ ".evalLock")
             $ show l

evalSrcLockProps :: Ident SourcePos -> Maybe (LockProperties SourcePos) -> TcDeclM PL.GlobalPol
evalSrcLockProps _ Nothing = return []
evalSrcLockProps i (Just (LockProperties _ lcs)) = do
  cs <- mapM (evalLClause i) lcs
--  debugPrint $ "Properties: " ++ show cs
  return cs

evalLClause :: Ident SourcePos -> LClause SourcePos -> TcDeclM PL.LockProp
evalLClause i (LClause _ cvds h atoms) = do
  tysCvds <- mapM evalClauseVarDecl cvds
  --(hActor, hActset, hTys) <- evalClauseHead tysCvds chead
  let allQs  = concatMap extractActors (h:atoms)
      actMap = zip allQs (map PL.QuantActor [0..])
      body   = map (PL.AtomPred . evalAtom actMap) atoms
  debugPrint $ "evalLClause: allQs: " ++ show allQs
  hAtom <- PL.AtomPred <$> evalSimpleAtom actMap i h
  domsQ <- mapM (evalActor tysCvds) allQs
  return $ PL.DatalogClause domsQ hAtom body

      where extractActors :: Atom SourcePos -> [Actor SourcePos]
            extractActors (Atom _ _ as) = as

evalClauseVarDecl :: ClauseVarDecl SourcePos -> TcDeclM (Ident SourcePos, TcRefType)
evalClauseVarDecl (ClauseVarDecl _ rt i) = do
  rTy <- evalSrcRefType genBot rt
  return (i, rTy)

--PL.DatalogClause <$> evalSimpleAtom i h <*> mapM evalAtom b
--evalLClause _ (ConstraintClause _ b) =
--    TcClause specialConstraintAtom <$> mapM evalAtom b

evalSimpleAtom :: [(Actor SourcePos, PL.ActorRep)] -> Ident SourcePos -> Atom SourcePos -> TcDeclM PL.TcAtom
evalSimpleAtom actMap i a@(Atom _ n _) = do
  TcClassT thisTypeName _tas <- getThisType
  debugPrint $ show thisTypeName
  case n of
    (Name _ _ mPre aI)
        | aI == i && (mPre == Nothing || mPre == Just thisTypeName)
            -> return $ evalAtom actMap a
    _ -> fail $ "Lock property head does not match lock name: " ++
                "\nExpected name: " ++ prettyPrint i ++
                "\nFound name: " ++ prettyPrint n

getActor :: ActorName SourcePos -> TcDeclM PL.TypedActorIdSpec
getActor (ActorName _ n) = do
  tm <- getTypeMap
  case lookupNamed actors n tm of
    Just aid -> return aid
    Nothing -> fail $ "getActor: No such actor: " ++ prettyPrint n
getActor (ActorTypeVar _ rt i) = do
  rTy <- evalSrcRefType genBot rt
  return $ PL.TypedActorIdSpec rTy $ PL.ActorTPVar (unIdent i)

freshActorId :: MonadBase m => String -> m PL.ActorIdentity
freshActorId = liftBase . PL.newFresh

unknownActorId :: MonadBase m => m PL.ActorIdentity
unknownActorId = liftBase PL.newUnknown

instanceActorId :: MonadBase m => Name SourcePos -> m PL.ActorIdentity
instanceActorId = liftBase . PL.newInstance

-----------------------------------------------------
-- Interpreting in the TcDeclM monad

lookupFieldD :: Name SourcePos -> TcDeclM Value
lookupFieldD n = do
  tm <- getTypeMap
  case lookupNamed policies n tm of
    Just p -> return $ VPol p
    Nothing -> do
      case lookupNamed actors n tm of
        Just aid -> return $ VAct aid
        Nothing ->
            case n of
              Name _ _ (Just tn@(Name _ TName _ _)) _ -> do
                _ <- fetchType tn
                lookupFieldD n
              _ -> do
                   fail $ "Referencing non-policy/actor field in typemethod: "
                            ++ prettyPrint n

{-
evalTypeMethod :: MethodInvocation SourcePos -> TcDeclM (PrgPolicy TcActor)
evalTypeMethod = interpretTypeMethod lookupFieldD
-}

{-----------------------------------------------------
-- The continuation monad

newtype TcDeclM r a = TcDeclM ((a -> TcBaseM r) -> TcBaseM r)

instance Monad (TcDeclM r) where
  return x = TcDeclM $ \k -> k x

  TcDeclM f >>= h = TcDeclM $ \k ->
                    f (\a -> let TcDeclM g = h a in g k)

  fail = liftTcBaseM . fail

-- instances

instance Functor (TcDeclM r) where
  fmap = liftM

instance Applicative (TcDeclM r) where
  (<*>) = ap
  pure = return

instance MonadTcBaseM (TcDeclM r) where
  liftTcBaseM dbma = TcDeclM $ \k -> dbma >>= k
  withTypeMap tmf (TcDeclM f) =
      TcDeclM $ \k -> do
        tm <- getTypeMap
        withTypeMap tmf $ f (\a -> withTypeMap (const tm) $ k a)

instance MonadIO (TcDeclM r) where
  liftIO = liftTcBaseM . liftIO

instance MonadBase (TcDeclM r) where
  liftBase = liftTcBaseM . liftBase

  withErrCtxt' ecf (TcDeclM f) =
      TcDeclM $ \k -> do
        ec <- liftBase getErrCtxt
        withErrCtxt' ecf $ f (\a ->
          (withErrCtxt' (const ec)) $ k a)

instance MonadPR (TcDeclM r) where
  liftPR = liftTcBaseM . liftPR

-- end instances

class MonadTcDeclM m where
  liftTcDeclM :: TcDeclM r a -> m r a

--  liftCallCC :: (((a -> TcDeclM r b) -> TcDeclM r a) -> TcDeclM r a)
--                -> ((a -> m r b) -> m r c) -> m r c

instance MonadTcDeclM TcDeclM where
  liftTcDeclM = id
--  liftTcDeclMWith = id
--  liftCallCC = id

-----------------------------------------------
-- Here's the whole reason why we go through
-- this lifting charade

callCC :: ((a -> TcDeclM r b) -> TcDeclM r a) -> TcDeclM r a
callCC cont = TcDeclM $ \k ->
                let TcDeclM g = cont (\a -> TcDeclM $ \_ -> k a) in g k

withTypeMapAlways :: (TypeMap -> TypeMap) -> TcDeclM r a -> TcDeclM r a
--withTypeMapAlways tmf tdm = callCC $ \cont -> do
--                              withTypeMap tmf $ tdm >>= cont

withTypeMapAlways tmf (TcDeclM f) = TcDeclM $ \k -> do
                                      withTypeMap tmf $ f k
-}

skolemTypeDecl :: TypeDecl SourcePos -> (TypeDecl SourcePos, TcClassType)
skolemTypeDecl td =
    case td of
      ClassTypeDecl sp (ClassDecl csp ms i tps sup impl cb) ->
          let (ty, subst) = skolemType i tps
              newCb = instantiate subst cb
          in (ClassTypeDecl sp $ ClassDecl csp ms i tps sup impl newCb, ty)
      ClassTypeDecl sp (EnumDecl esp ms i impl eb) -> -- Cannot be parameterized
          let (ty, _subst) = skolemType i []
          in (ClassTypeDecl sp $ EnumDecl esp ms i impl eb, ty)
      InterfaceTypeDecl sp (InterfaceDecl isp ms i tps sups ib) ->
          let (ty, subst) = skolemType i tps
              newIb = instantiate subst ib
          in (InterfaceTypeDecl sp $ InterfaceDecl isp ms i tps sups newIb, ty)




skolemType :: Ident SourcePos -> [TypeParam SourcePos] -> (TcClassType, [(TypeParam SourcePos, TcTypeArg)])
skolemType i tps =
    let args = map skolemParam tps
    in (TcClassT (mkSimpleName TName i) args, zip tps args)

skolemParam :: TypeParam SourcePos -> TcTypeArg
skolemParam tp =
    case tp of
      TypeParam _ i _    ->
          TcActualType (TcClsRefT (TcClassT (mkSimpleName TName i) []))
      ActorParam  _ _rt i    ->
          TcActualActor (PL.TypedActorIdSpec undefined $ PL.ActorTPVar $ unIdent i)
          -- It's actually fine to use undefined here, as we will always force a type
          -- on it when using it in instantiation in "skolemTypeDecl".
      PolicyParam _ i    ->
          TcActualPolicy (PL.VarPolicy $ PL.PolicyVar $ PL.PolicyTypeParam $ unIdent i)
      LockStateParam _ i ->
          TcActualLockState [PL.LockTypeParam $ unIdent i]


-----------------------------------------------
-- Underlying non-cont'ed monad

newtype TcDeclM a = TcDeclM (TypeMap -> TypeMap -> TcClassType -> PiReader (a, TypeMap) )

runTcDeclM :: TcClassType -> TcDeclM a -> PiReader a
runTcDeclM ty (TcDeclM f) = fst <$> f emptyTM emptyTM ty

instance Fail.MonadFail TcDeclM where
  fail = liftPR . fail

instance Monad TcDeclM  where
  return = liftPR . return

  TcDeclM f >>= k = TcDeclM $ \ !ctm !gtm !ty -> do
                       (a, gtm') <- f ctm gtm ty
                       let TcDeclM g = k a
                       g ctm gtm' ty

  fail = Fail.fail

instance Functor TcDeclM  where
  fmap = liftM

instance Applicative TcDeclM  where
  pure = return
  (<*>) = ap

instance MonadIO TcDeclM  where
  liftIO = liftPR . liftIO

instance MonadBase TcDeclM  where
  liftBase = liftPR . liftBase
  withErrCtxt' prf (TcDeclM f) = TcDeclM $ \ctm gtm ty -> withErrCtxt' prf $ f ctm gtm ty
  tryM (TcDeclM f) = TcDeclM $ \ctm gtm ty -> do
                             esatm <- tryM (f ctm gtm ty)
                             case esatm of
                               Right (a, tm) -> return (Right a, tm)
                               Left err -> return (Left err, gtm)
  failE = liftPR . failE
  failEC x = liftPR . failEC x

instance MonadPR TcDeclM  where
  liftPR pra = TcDeclM $ \_ gtm _ -> pra >>= \a -> return (a, gtm)

class MonadPR m => MonadTcDeclM m where
  liftTcDeclM :: TcDeclM a -> m a
  withCurrentTypeMap :: (TypeMap -> Either Error TypeMap) -> m a -> m a

instance MonadTcDeclM TcDeclM  where
  liftTcDeclM = id
  withCurrentTypeMap = withCurrentTypeMapTB


extendGlobalTypeMap :: MonadTcDeclM m => (TypeMap -> TypeMap) -> m ()
extendGlobalTypeMap = liftTcDeclM . extendGlobalTypeMapTB


getTypeMap :: MonadTcDeclM m => m TypeMap
getTypeMap = liftTcDeclM getTypeMapTB

getThisType :: MonadTcDeclM m => m TcClassType
getThisType = liftTcDeclM getThisTypeTB

withThisType :: TcClassType -> TcDeclM a -> TcDeclM a
withThisType ct (TcDeclM f) =
    TcDeclM $ \ctm gtm _oldty -> f ctm gtm ct

getThisStateType :: MonadTcDeclM m => m TcStateType
getThisStateType = do
  ct <- getThisType
  (is, tsig) <- lookupTypeOfType $ clsTypeToType ct
  -- We assume here that the TypedActorIdSpec points to the correct refType already
  let aids = mapMaybe (\(_,i) -> Map.lookup i $ actors $ tMembers tsig) is
      thisId = PL.TypedActorIdSpec (TcClsRefT ct) PL.ThisId
  return $ instanceT (TcClsRefT ct) thisId aids (NotNull, Committed) --Is it correct ?


getSuperType :: MonadTcDeclM m => m TcClassType
getSuperType = do
  thisTy <- getThisType
  (_, thisSig) <- lookupTypeOfType (clsTypeToType thisTy)
  case tSupers thisSig of
    [] -> return objectT
    [s] -> return s
    _  -> panic (tcDeclMModule ++ ".getSuperType")
          "Called on non-class with multiple super types"


withFreshCurrentTypeMap :: TcDeclM a -> TcDeclM a
withFreshCurrentTypeMap = withCurrentTypeMap (return . const emptyTM)

getLocalTypeMap :: MonadTcDeclM m => m TypeMap
getLocalTypeMap = liftTcDeclM $
     TcDeclM $ \ctm gtm _ -> return (ctm, gtm)

getTypeMapTB :: TcDeclM TypeMap
getTypeMapTB = TcDeclM $ \ctm gtm _ -> return (ctm `merge` gtm, gtm)

getThisTypeTB :: TcDeclM TcClassType
getThisTypeTB = TcDeclM $ \_ gtm ty -> return (ty, gtm)

withCurrentTypeMapTB ::  (TypeMap -> Either Error TypeMap) -> TcDeclM a -> TcDeclM a
withCurrentTypeMapTB tmf (TcDeclM f) = TcDeclM $ \ctm gtm ty ->
  case tmf ctm of
    Right tm -> f tm gtm ty
    Left err -> failE err

extendGlobalTypeMapTB :: (TypeMap -> TypeMap) -> TcDeclM ()
extendGlobalTypeMapTB tmf = TcDeclM $ \_ gtm _ -> return ((), tmf gtm)


genBot, genMeta :: (MonadTcDeclM m, HasSubTyping m) => m PL.ActorPolicy
genBot = PL.bottomM
genMeta = newMetaPolVar $ Ident defaultPos (B.pack "<array>")

newMetaPolVar :: MonadTcDeclM m => Ident SourcePos -> m PL.ActorPolicy
newMetaPolVar i = liftTcDeclM $ do
  uniq <- getFreshInt
  return $ PL.MetaVar (PL.MetaVarRep uniq $ unIdent i)
