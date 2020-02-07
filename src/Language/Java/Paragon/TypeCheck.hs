module Language.Java.Paragon.TypeCheck (typeCheck, T) where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.Error
import Language.Java.Paragon.SourcePos

import qualified Language.Java.Paragon.PolicyLang as PL

import Language.Java.Paragon.TypeCheck.TcExp
import Language.Java.Paragon.TypeCheck.TcStmt
import Language.Java.Paragon.TypeCheck.Monad

import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.TypeMap
import Language.Java.Paragon.TypeCheck.NullAnalysis

import Control.Monad (unless, foldM, foldM_)
import qualified Data.Map as Map
import Data.Map((!))
import qualified Data.Set as Set
import qualified Data.ByteString.Char8 as B
import Data.Maybe
import Data.List (intercalate, unzip4)
import Control.Applicative ((<$>))
import Control.Arrow (second)

-- | Generate
typeCheck :: PiPath -- ^ Paths to pi files
          -> String -- ^ Base name of the file
          -> TypeCheck BaseM CompilationUnit -- ASK where does TypeCheck come
          -- from, why seems like has no return type?
typeCheck piDirs baseName (CompilationUnit _ pkg imps [td]) = do
      let (fullTd, skoTy) = skolemTypeDecl td
      runPiReader piDirs $ runTcDeclM skoTy $ do
                 let mPkgPrefix = fmap (\(PackageDecl _ n) -> n) pkg
                 typedTd <- typeCheckTd baseName mPkgPrefix fullTd
                 return (CompilationUnit Nothing
                           (fmap notAppl pkg) (map notAppl imps) [typedTd])

typeCheck _ _ _ =
    do fail $ "\n\n" ++ "Encountered multiple type declarations in the same file"

-------------------------------------------------------------------------------------
-- Here goes TcTypeDecl.hs

typeCheckTd :: String -> Maybe (Name SourcePos) -> TypeCheck TcDeclM TypeDecl
typeCheckTd baseName mpkg (ClassTypeDecl     _ cdecl)
    = ClassTypeDecl Nothing <$> typeCheckCd baseName mpkg cdecl
typeCheckTd baseName mpkg (InterfaceTypeDecl _ idecl)
    = InterfaceTypeDecl Nothing <$> typeCheckId baseName mpkg idecl

typeCheckId :: String -> Maybe (Name SourcePos) -> TypeCheck TcDeclM InterfaceDecl
typeCheckId baseName mpkg (InterfaceDecl sp _ms i tps supers (InterfaceBody _ memberDecls)) = do
  --debug "typeCheckId"
  withErrCtxt (FallbackContext ("When checking interface " ++ prettyPrint i)) $ do
  check (unIdent i == B.pack baseName) $ mkError (FileInterfaceMismatch $ B.unpack (unIdent i)) sp
  staticWPol <- PL.topM
  registerThisType mpkg i tps supers
  withFoldMap withTypeParam tps $
   typeCheckActorFields memberDecls $ do
    --debug "typeCheckLockDecls start"
    typeCheckTMPolLocks memberDecls $ do
{-    typeCheckLockDecls memberDecls $ do
    --debug "typeCheckTypeMethods start"
    typeCheckTypeMethods memberDecls $ do
    --debug "typeCheckPolicyFields start"
    typeCheckPolicyFields memberDecls $ do -}
     --debug "typeCheckSignatures start"
     typeCheckSignatures memberDecls $ \constrWPol -> do
      registerThisTypeSigs mpkg i tps supers
      --debug "typeCheckMemberDecls start"
      InterfaceDecl Nothing (map notAppl _ms) (notAppl i)
        (map notAppl tps) (map notAppl supers) .
          InterfaceBody Nothing <$>
            typeCheckMemberDecls staticWPol constrWPol memberDecls

typeCheckCd :: String -> Maybe (Name SourcePos) -> TypeCheck TcDeclM ClassDecl
typeCheckCd baseName mpkg (ClassDecl sp ms i tps mSuper _impls (ClassBody _ decls)) = do
  --debug "typeCheckCd"
  withErrCtxt (ClassContext (prettyPrint i)) $ do

  -- Check that the class has the same name as the file it is defined in
  check (unIdent i == B.pack baseName) $ mkError (FileClassMismatch $ B.unpack (unIdent i)) sp

  -- Determine if class has a static initializer effect bound
  staticWPol <- PL.VarPolicy <$> getWritePolicy ms

  let memberDecls = [ mdecl | MemberDecl _ mdecl  <- decls ]
      inits       = [ idecl | idecl@InitDecl {}   <- decls ]
      supers      = maybe [objectType] (:[]) mSuper
  withFoldMap withTypeParam tps $ do
  registerThisType mpkg i tps supers
--  withFoldMap withSuperType (maybe [] (:[]) mSuper) $ do

  -- This is where the real fun starts.
  -- First we check all "actor fields", i.e. all final fields with a reference type.
  -- These are stored away in the typemap for this file.
  typeCheckActorFields memberDecls $ do
--    debugPrint "typeCheckLockDecls start"
    typeCheckTMPolLocks memberDecls $ do
{-    debugPrint "typeCheckLockDecls start"
    typeCheckLockDecls memberDecls $ do
    debugPrint "typeCheckTypeMethods start"
    typeCheckTypeMethods memberDecls $ do
    debugPrint "typeCheckPolicyFields start"
    typeCheckPolicyFields memberDecls $ do -}
     debugPrint "typeCheckSignatures start"
     typeCheckSignatures memberDecls $ \constrWPol -> do
        registerThisTypeSigs mpkg i tps supers
        ClassDecl Nothing (map notAppl ms) (notAppl i)
          (map notAppl tps) (fmap notAppl mSuper) (map notAppl _impls) .
            ClassBody Nothing <$> do
              --debug "typeCheckInitDecls start"
              inits' <- typeCheckInitDecls staticWPol constrWPol inits
              --debug "typeCheckMemberDecls start"
              mDs'   <- typeCheckMemberDecls staticWPol constrWPol memberDecls
              return (inits' ++ map (MemberDecl Nothing) mDs')

typeCheckCd _ _ _ = panic (typeCheckerBase ++ ".typeCheckCd")
                  "Enum decls not yet supported"

objectType :: ClassType SourcePos
objectType = ClassType defaultPos
              (mkName_ TName PName $
               map (Ident defaultPos . B.pack) ["java","lang","Object"]) []

registerThisType :: Maybe (Name SourcePos)
                 -> Ident SourcePos
                 -> [TypeParam SourcePos]
                 -> [ClassType SourcePos]
                 -> TcDeclM ()
registerThisType pkgPre i tps supers = do
    cTys   <- mapM (evalSrcClsType genBot) supers
    baseTm <- getTypeMap
    let superTMs = flip map cTys $ \cTy ->
                     case lookupTypeOfT (clsTypeToType cTy) baseTm of
                       Left mErr
                           -> panic (typeCheckerBase ++ ".withSuperType")
                              $ "Super type evaluated but now doesn't exist: " ++ show mErr
                       Right (_,superSig) -> (tMembers superSig) -- { constrs = Map.empty }

    -- We insert an empty typemap at first,
    -- since we are only using this when checking signatures
    let iN    = Name defaultPos TName Nothing i
        fullN = Name defaultPos TName pkgPre  i
        thisTM = foldl merge emptyTM superTMs
        thisSig = TSig (TcClsRefT $ TcClassT fullN [])
                        True False cTys [] thisTM
    --debugPrint $ "regThisType[thisTM]:\n " ++ prettyPrint thisTM -- show (methods thisTM)
    extendGlobalTypeMap (extendTypeMapT iN    tps [] thisSig)
    unless (isNothing pkgPre) $
         extendGlobalTypeMap (extendTypeMapT fullN tps [] thisSig)


registerThisTypeSigs :: Maybe (Name SourcePos) -> Ident SourcePos
                     -> [TypeParam SourcePos] -> [ClassType SourcePos] -> TcDeclM ()
registerThisTypeSigs pkgPre i tps supers = do
  cTys   <- mapM (evalSrcClsType genBot) supers
  baseTm <- getTypeMap
  -- debugPrint $ "Current typemap: " ++ show baseTm
  let superTMs = flip map cTys $ \cTy ->
                     case lookupTypeOfT (clsTypeToType cTy) baseTm of
                       Left mErr
                           -> panic (typeCheckerBase ++ ".withSuperType")
                              $ "Super type evaluated but now doesn't exist: " ++ show mErr
                       Right (_,superSig) -> tMembers superSig -- { constrs = Map.empty }

  let iN    = Name defaultPos TName Nothing i
      fullN = Name defaultPos TName pkgPre  i
      thisTm = baseTm { types = Map.empty, packages = Map.empty } -- Should be identity transformation
      resTm  = foldl merge thisTm superTMs
      thisSig = TSig (TcClsRefT $ TcClassT fullN [])
                  True False cTys [] resTm -- TODO: Include proper values
  --debugPrint $ "regThisTypeSigs: " ++ show (methods resTm)
  extendGlobalTypeMap (merge resTm)
  extendGlobalTypeMap (extendTypeMapT iN    tps [] thisSig)
  unless (isNothing pkgPre) $
       extendGlobalTypeMap (extendTypeMapT fullN tps [] thisSig)


---------------------------------------------------------------
-- Actors

-- TODO: We may have a problem with boot-strapping here.
-- We can stay clear of the problem for now, using careful
-- Paragon coding, but we need to think about it and fix it eventually.
typeCheckActorFields :: [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
typeCheckActorFields mDecls tcba = do
    --debug "fetchActors"
    let acts = [ (ms, rt, vd)
                     | FieldDecl _ ms (RefType _ rt) vds <- mDecls
                     , Final defaultPos `elem` ms
                     , vd <- vds
                     -- Only final ones can be used in policies
               ]
    debugPrint $ "Actors: " ++ show acts ++ "\n"
    --let -- (sfs,unstables)  = partition (\(ms, _) -> Static () `elem` ms) acts
    --    (spawns,stables) = partition (\(_,_,VarDecl _ _ initz) -> initz == Nothing) acts -- sfs

    --withFoldMap spawnActorVd spawns $
--      withFoldMap unknownActorVd unstables $
    withFoldMap evalActorVd acts {-stables-} $ do
        debugPrint "fetchActors complete"
        tcba

            where evalActorVd :: ([Modifier SourcePos], RefType SourcePos, VarDecl SourcePos)
                      -> TcDeclM a -> TcDeclM a

{-                  -- All non-final OR non-static
                  unknownActorVd (ms, VarDecl _ (VarId _ i) _) tcra = do
                    p <- getReadPolicy ms
                    let vti = VSig actorT p False (Static () `elem` ms) (Final () `elem` ms)
                    a <- unknownActorId
                    withTypeMap (\tm ->
                                     tm { actors = Map.insert i a (actors tm),
                                          fields = Map.insert i vti (fields tm) }) $
                      tcra
                  unknownActorVd (_, VarDecl _ arvid _) _ =
                      fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid
-}
                  -- Final
                  evalActorVd (_ms, rt, VarDecl _sp (VarId _ i) mInit) tcra = do
                    rTy <- evalSrcRefType genBot rt
--                    p <- PL.VarPolicy <$> getReadPolicy ms
--                    let vti = VSig (TcRefT rTy) p False
--                              (Static defaultPos `elem` ms) (Final defaultPos `elem` ms) False

                    a <- case mInit of
                           Just (InitExp _ e) -> do
                              case e of
                                ExpName _ n -> do
                                       tm <- getTypeMap
                                       case lookupNamed actors n tm of
                                         Just a -> return a
                                         Nothing -> PL.TypedActorIdSpec rTy .
                                                    PL.ConcreteActorId <$> unknownActorId
                                InstanceCreation {} -> do
                                  PL.TypedActorIdSpec rTy .
                                   PL.ConcreteActorId <$> freshActorId (B.unpack $ unIdent i)
                                _ -> PL.TypedActorIdSpec rTy .
                                      PL.ConcreteActorId <$> unknownActorId
                           Nothing -> PL.TypedActorIdSpec rTy .
                                       PL.ConcreteActorId <$> unknownActorId
                    debugPrint $ "Evaluated field \"" ++ prettyPrint i ++ "\" to have actor id: " ++ prettyPrint a
{- -- Added by Dima:
                    withCurrentTypeMap (\tm ->
                      let iName = unIdent i
                          tmFields = fields tm
                      in if Map.notMember iName tmFields
                           then return $ tm { actors = Map.insert iName a (actors tm)},
                                              fields = Map.insert iName vti tmFields }
                           else failEither $ mkError (FieldAlreadyDefined (B.unpack iName)) sp) $
-- to here -}
                    withCurrentTypeMap (\tm -> return $ tm { actors = Map.insert (unIdent i) a (actors tm) }) tcra
--                  evalActorVd (_,_, VarDecl _ _ Nothing) _ = panic (typeCheckerBase ++ ".evalActorVd") $ "No initializer"
                  evalActorVd (_,_, VarDecl _ arvid _)   _ = fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

-- end actors

---------------------------------------------------------------
-- Policies, typemethods and locks

typeCheckTMPolLocks :: [MemberDecl SourcePos] -> TcDeclM a -> TcDeclM a
typeCheckTMPolLocks = withFoldMap typeCheckTMPolLock

typeCheckTMPolLock :: MemberDecl SourcePos -> TcDeclM a -> TcDeclM a
typeCheckTMPolLock md@LockDecl{} tcba = typeCheckLockDecl md tcba
typeCheckTMPolLock md@(MethodDecl _ ms _ _ _ _ _ _) tcba
                   | Typemethod defaultPos `elem` ms = typeCheckTMSig md $ do
                                                 st <- setupStartState
                                                 _ <- typeCheckMethodDecl st md
                                                 addTMBody md tcba
typeCheckTMPolLock md@(FieldDecl _ ms (PrimType _ (PolicyT _)) _) tcba
                   | Final defaultPos `elem` ms = typeCheckPolicyField md tcba
typeCheckTMPolLock _ tcba = tcba

---------------------------------------------------------------
-- Locks
{-
typeCheckLockDecls :: [MemberDecl ()] -> TcDeclM a -> TcDeclM a
typeCheckLockDecls mds tcba = do
  let ls = [ ld | ld@ LockDecl {} <- mds ]
  withFoldMap typeCheckLockDecl ls $ tcba
-}
typeCheckLockDecl :: MemberDecl SourcePos -> TcDeclM a -> TcDeclM a
typeCheckLockDecl (LockDecl _ ms i rts mProps) tcba = do
  lsig <- withErrCtxt (LockSignatureContext (prettyPrint i)) $ do
    let rPolExps = [ e | Reads _ e <- ms ]
    check (length rPolExps <= 1) $ toUndef
              "At most one read modifier allowed per field"
    mapM_ (typeCheckPolicyMod emptyCodeState) rPolExps
    pol <- getLockPolicy ms
    rTys <- mapM (evalSrcRefType genBot) rts
    shortProps <- getLockModProps Nothing i ms
    prs <- evalSrcLockProps i mProps
    return $ LSig (PL.VarPolicy pol) rTys (shortProps ++ prs)
  withCurrentTypeMap (\tm -> return $ tm { locks = Map.insert (unIdent i) lsig (locks tm) })
    tcba

--typeCheckLockDecl (LockDecl _ _ _ _ _) _ = fail $ "Lock properties not yet supported"
typeCheckLockDecl md _ = panic (typeCheckerBase ++ ".typeCheckLockDecl") $
                         "Applied to non-lock decl " ++ show md
-- end Locks
---------------------------------------------------------------
-- Typemethods
{-
typeCheckTypeMethods :: [MemberDecl ()] -> TcDeclM a -> TcDeclM a
typeCheckTypeMethods mds tcba = do
  let tms = [ tmd | tmd@(MethodDecl _ ms _ _ _ _ _ _) <- mds,
                    Typemethod () `elem` ms
            ]
  withFoldMap typeCheckTMSig tms $ do
    st <- setupStartState
    mapM_ (typeCheckMethodDecl st) tms
    withFoldMap addTMBody tms $
      tcba
-}
-- Precondition: only applied on actual typemethods
typeCheckTMSig :: MemberDecl SourcePos -> TcDeclM a -> TcDeclM a
typeCheckTMSig (MethodDecl _ ms tps retT i ps exns _) tcba = do
  newMethMap <- withErrCtxt (FallbackContext ("When checking signature of typemethod "
                               ++ prettyPrint i)) $ do
    -- 1. No type parameters
    check (null tps) $ toUndef "No type parameters allowed on typemethod methods"
    -- 2. No interaction with policies or lock states
    check (all (\m -> not (isPolicyMod m || isLockStateMod m)) ms) $ toUndef
          "Methods annotated with typemethod cannot have policy or lock state modifiers"
    -- 3. Same check for parameters
    let (pis, pmss) = unzip [ (unIdent pI, pms) | FormalParam _ pms _ _ (VarId _ pI) <- ps ]
        plms = [ m | m <- concat pmss, isPolicyMod m, isLockStateMod m ]
        nnp = [ pid | (pid, pms) <- zip pis pmss, Notnull defaultPos `elem` pms]
    check (null plms) $ toUndef "Parameters to typemethods must not have policy modifiers"
    -- 4. No exceptions may be thrown
    check (null exns) $ toUndef "Methods annotated with typemethod may not throw exceptions"
    tyPs <- mapM (evalSrcType genBot) [ t | FormalParam _ _ t _ _ <- ps ]
    rTy <- evalReturnType genBot retT
    tp <- PL.topM
    bt <- PL.bottomM
    let mti = MSig {
              mRetType = rTy,
              mModifiers = removeAnnotationMany ms,
              mRetPol  = bt,
              mWrites  = tp,
              mPars    = pis,
              mParBounds = [ bt | _ <- ps ],
              mExpects = [],
              mLMods   = PL.noDelta,
              mExns    = [],
              mNNPars  = nnp,
              mIsNative = Native defaultPos `elem` ms
            }
        isVarArity = case reverse ps of
                       [] -> False
                       (FormalParam _ _ _ b _ : _) -> b
        newMethMap = Map.singleton (tps, tyPs, isVarArity) mti
    return newMethMap

  withCurrentTypeMap (\tm -> return $ tm { methods = Map.insertWith Map.union (unIdent i) newMethMap (methods tm) })
       tcba

typeCheckTMSig md _ = panic (typeCheckerBase ++ ".typeCheckTMSig") $
                      "Applied to non-method decl " ++ show md

addTMBody :: MemberDecl SourcePos -> TcDeclM a -> TcDeclM a
addTMBody (MethodDecl _ _ _ _ i ps _ (MethodBody _ (Just bl))) =
    let pis = [ unIdent iP | FormalParam _ _ _ _ (VarId _ iP) <- ps ]
    in withCurrentTypeMap $ \tm -> return $ tm { typemethods = Map.insert (unIdent i) (pis,bl) (typemethods tm) }
addTMBody md = panic (typeCheckerBase ++ ".addTMBody") $
               "Applied to non-method decl " ++ show md

-- end Typemethods
-------------------------------------------------------------------------------------
-- Policies
{-
typeCheckPolicyFields :: [MemberDecl ()] -> TcDeclM a -> TcDeclM a
typeCheckPolicyFields mds =
    let pfs = [ pf | pf@(FieldDecl _ ms (PrimType _ (PolicyT _)) _) <- mds,
                     Final () `elem` ms
              ] in
    -- The 'map' here means fields can only refer to things above them
    withFoldMap typeCheckPolicyField pfs
-}
-- Precondition: only apply on policies
typeCheckPolicyField :: MemberDecl SourcePos -> TcDeclM a -> TcDeclM a
typeCheckPolicyField fd@(FieldDecl _ ms t vds) tcba = do
  --debug "typeCheckPolicyField"
  -- 0. Flatten
  let pols = [ (i, initz) | VarDecl _ (VarId _ i) initz <- vds ]
  vti <- withErrCtxt (FallbackContext ("When checking policy fields "
                 ++ intercalate ", " (map (prettyPrint . fst) pols))) $ do


    -- 1. Check that initializer exists
    check (all ((/= Nothing) . snd) pols) $ toUndef
               "typeCheckPolicyField: Uninitialized policy"
    -- 2. Check that policy is bottom
    check (null [ () | Reads _ _ <- ms ]) $ toUndef
               "typeCheckPolicyField: Policy must have policy bottom"
    -- 3. Add signature to environment
    tcty <- evalSrcType genMeta t
    bt <- PL.bottomM
    return $ VSig {
                varType = tcty,
                varPol  = bt,
                varParam = False,
                varStatic = Static defaultPos `elem` ms,
                varFinal  = Final  defaultPos `elem` ms,
                varNotnull = False
              }
  withFoldMap (addField vti) (map fst pols) $ do
    -- 4. Typecheck the field normally
    st <- setupStartState
    tp <- PL.topM
    _  <- typeCheckFieldDecl tp tp st fd
    -- 5. Evaluate the initializers
    withFoldMap (evalAddPolicyInit st) (map (second fromJust) pols)
      tcba

          where
            addField :: VarFieldSig -> Ident SourcePos -> TcDeclM a -> TcDeclM a
            addField vti i =
                    withCurrentTypeMap $ \tm ->
                      let Ident sp iName = i
                          tmFields = fields tm
                      in if Map.notMember iName tmFields
                           then return $ tm { fields = Map.insert iName vti tmFields }
                           else failEither $ mkError (PolicyAlreadyDefined (B.unpack iName)) sp

typeCheckPolicyField fd _ = panic (typeCheckerBase ++ ".typeCheckPolicyField") $
                           "Applied to non-policy decl " ++ show fd

evalAddPolicyInit :: CodeState -> (Ident SourcePos, VarInit SourcePos) -> TcDeclM a -> TcDeclM a
evalAddPolicyInit st (i, InitExp _ eInit) tcba = do
  --debug $ "evalAddInit: " ++ show i
  tp <- PL.topM
  tcPol <- withErrCtxt (FallbackContext ("When evaluating the initializer of field "
                          ++ prettyPrint i)) $ evalPolicy eInit
  ((tyInit, _pInit, _eInit'),_) <- runTcCodeM (simpleEnv tp False "policy initializer" False) st $ tcExp eInit
  check (isPolicyType tyInit) $ toUndef $
        "Cannot initialize policy field " ++ prettyPrint i ++
        " with non-policy expression " ++ prettyPrint eInit ++ " of type " ++ prettyPrint tyInit
  withCurrentTypeMap (\tm -> return $ tm { policies = Map.insert (unIdent i) tcPol (policies tm) })
    tcba
evalAddPolicyInit _ (i, arrInit) _ =
    fail $ "Cannot initialize policy field " ++ prettyPrint i ++
           " with array " ++ prettyPrint arrInit
-- end policies
------------------------------------------------------------------------------
-- Signatures

typeCheckSignatures :: [MemberDecl SourcePos] -> (ActorPolicy -> TcDeclM a) -> TcDeclM a
typeCheckSignatures mds tcbaf = do
  debugPrint "Entering typeCheckSignatures..."
  st <- setupStartState
  withFoldMap (typeCheckSignature st) mds $ do
    debugPrint "Done with typeCheckSignatures"
    getConstrPol >>= tcbaf

getConstrPol :: TcDeclM ActorPolicy
getConstrPol = do
  mConstrs <- constrs <$> getTypeMap
  let wPols = map cWrites $ Map.elems mConstrs
  bt <- PL.bottomM
  foldM PL.lub bt wPols

typeCheckSignature :: CodeState -> MemberDecl SourcePos -> TcDeclM a -> TcDeclM a
-- Fields
typeCheckSignature st _fd@(FieldDecl _ ms t vds) tcba
    | t /= PrimType defaultPos (PolicyT defaultPos) = do
  debugPrint $ "typeCheckSignature: " ++ prettyPrint _fd
  let fis = [ i | VarDecl _ (VarId _ i) _ <- vds ]
  vti <- withErrCtxt (FallbackContext ("When checking signature for fields "
                      ++ intercalate ", " (map prettyPrint fis))) $ do
    -- 1. Check field type
    ty <- evalSrcType genMeta t
    debugPrint $ "Type evaluated to: " ++ show ty
    -- _  <- lookupTypeOfT ty <$> getTypeMap -- TODO
    -- 2. Typecheck and evaluate field policy
    let rPolExps = [ e | Reads _ e <- ms ]
    check (length rPolExps <= 1) $ toUndef
              "At most one read modifier allowed per field"
    mapM_ (typeCheckPolicyMod st) rPolExps
    rPol <- getReadPolicy ms
    check (Final defaultPos `elem` ms || not (PL.includesThisVP rPol)) $ toUndef $
          prettyPrint (PL.thisP :: PL.PrgPolicy) ++
          " may not be used as the policy of non-final fields"

    check (not $ typeIncludesThis ty) $ toUndef $
          prettyPrint (PL.thisP :: PL.PrgPolicy) ++
          " may not be used in the type arguments of a field type"

    -- 3. Add signature to typemap
    return $ VSig {
                 varType = ty,
                 varPol  = PL.VarPolicy rPol,
                 varParam  = False,
                 varStatic = Static defaultPos `elem` ms,
                 varFinal  = Final  defaultPos `elem` ms,
                 varNotnull = Notnull defaultPos `elem` ms
               }
  withFoldMap (addField vti) vds
    tcba

        where addField :: VarFieldSig -> VarDecl SourcePos -> TcDeclM a -> TcDeclM a
              addField vti (VarDecl sp (VarId _ i) _) =
                  withCurrentTypeMap $ \tm ->
                    let iName = unIdent i
                        tmFields = fields tm
                    in {- NB: Removing this filter since actors are no longer checked as fields in the actor stage
                      if Map.member iName (actors tm)
                         then return tm
                         else -}
                       if Map.notMember iName tmFields
                                then return $ tm { fields = Map.insert iName vti tmFields }
                                else failEither $ mkError (FieldAlreadyDefined (B.unpack iName)) sp
              addField _ vd = \_ -> fail $ "Deprecated declaration: " ++ prettyPrint vd

              typeIncludesThis :: TcType -> Bool
              typeIncludesThis (TcRefT rt) = refTypeIncludesThis rt
              typeIncludesThis _ = False

              refTypeIncludesThis :: TcRefType -> Bool
              refTypeIncludesThis rTy =
                  case rTy of
                    TcArrayT arrTy arrPol ->
                        typeIncludesThis arrTy || PL.includesThis arrPol
                    TcClsRefT (TcClassT _ targs) ->
                        any argIncludesThis targs
                    _ -> False

              argIncludesThis :: TcTypeArg -> Bool
              argIncludesThis targ =
                  case targ of
                    TcActualType rt -> refTypeIncludesThis rt
                    TcActualPolicy p -> PL.includesThis p
                    _ -> False

-- Methods
typeCheckSignature st (MethodDecl sp ms tps retT i ps exns _mb) tcba
    | Typemethod defaultPos `notElem` ms = do
  -- debug $ "typeCheckSignature: " ++ prettyPrint (MethodDecl () ms tps retT i ps exns (MethodBody () Nothing))
  newMethMap <- withErrCtxt (FallbackContext ("When checking signature of method " ++ prettyPrint i ++ "("
                             ++ intercalate ", " [prettyPrint t | FormalParam _ _ t _ _ <- ps ] ++ ")")) $ do
    -- 0. Setup type params
    withFoldMap withTypeParam tps $ do
    -- 1. Check return type
    ty <- evalReturnType genBot retT
    -- 2. Check parameter types and policy modifiers
    (pTs,pIs,pPols,pMnn) <- unzip4 <$> mapM (typeCheckParam st) ps
    let pInfos = zip3 ps pTs pPols
    -- 3. Typecheck and evaluate policy modifiers
    withFoldMap withParam pInfos $ checkPolicyMods st ms
      "typeCheckSignature: At most one return/write modifier allowed per method"
    -- 4. Typecheck and evaluate lock modifiers
    lms <- checkLMMods ms
    es  <- checkExpectsMods ms
    -- 5. Typecheck and evaluate exception signatures
    xSigs <- withFoldMap withParam pInfos $ mapM (typeCheckExnSig st) exns
    -- 6. Add signature to typemap
    rPol <- getReturnPolicy ms pPols -- IF GENERIC: map (TcRigidVar True) pIs
    wPol <- getWritePolicy ms
    --debugPrint $ "Method " ++ prettyPrint i ++ " has wPol: " ++ show wPol
    let pnn = [x | (Just x) <- pMnn]
        mti = MSig {
                mRetType = ty,
                mModifiers = removeAnnotationMany ms,
                mRetPol  = PL.VarPolicy rPol,
                mWrites  = PL.VarPolicy wPol,
                mPars    = pIs,
                mParBounds = map PL.VarPolicy pPols,
                mExpects = es,
                mLMods   = lms,
                mExns    = xSigs,
                mNNPars  = pnn,
                mIsNative = Native defaultPos `elem` ms
              }
        isVarArity = case reverse ps of
                       [] -> False
                       (FormalParam _ _ _ b _ : _) -> b
    return $ Map.singleton (tps, pTs, isVarArity) mti

  withCurrentTypeMap (\tm -> do
      let newTm = tm { methods = Map.insertWith Map.union (unIdent i) newMethMap (methods tm) }
      if isOverloaded (methods newTm) (methods tm)
        then return newTm
        else failEither $ mkError (MethodAlreadyDefined $ B.unpack (unIdent i)) sp)
    tcba
  where
    -- Map.union did the job of checking for overloading because of the nature of keys
    -- isOverloaded just checks if the method is completely new or that the size of
    -- methods map is changed. If it is unchanged, then the overloading is wrong and union
    -- has overwritten previous method signature.
    isOverloaded newMap oldMap =
      let iName = unIdent i
      in Map.notMember iName oldMap ||
         Map.size (newMap ! iName) /= Map.size (oldMap ! iName)

-- Constructors
typeCheckSignature st (ConstructorDecl sp ms tps i ps exns _mb) tcba = do
  (pTs, isVA, cti) <- withErrCtxt (FallbackContext ("When checking signature of constructor " ++ prettyPrint i ++ "("
                             ++ intercalate ", " [prettyPrint t | FormalParam _ _ t _ _ <- ps ] ++ ")")) $ do
    -- 0. Setup type parameters
    withFoldMap withTypeParam tps $ do
    -- 1. Check parameter types and policy modifiers
    (pTs,pIs,pPols,pMnn) <- unzip4 <$> mapM (typeCheckParam st) ps
    let pInfos = zip3 ps pTs pPols
    -- 2. Typecheck and evaluate policy modifiers
    withFoldMap withParam pInfos $ checkPolicyMods st ms
      "typeCheckSignature: At most one return/write modifier allowed per constructor"
    -- 3. Typecheck and evaluate lock modifiers
    lms <- checkLMMods ms
    es  <- checkExpectsMods ms
    -- 4. Typecheck and evaluate exception signatures
    xSigs <- withFoldMap withParam pInfos $ mapM (typeCheckExnSig st) exns
    -- 5. Add signature to typemap
    wPol <- getWritePolicy ms
    let pnn = [x | (Just x) <- pMnn]
        cti = CSig {
              cWrites  = PL.VarPolicy wPol,
              cPars    = pIs,
              cParBounds = map PL.VarPolicy pPols,
              cExpects = es,
              cLMods   = lms,
              cExns    = xSigs,
              cNNPars  = pnn,
              cIsNative = False
            }
        isVarArity = case reverse ps of
                       [] -> False
                       (FormalParam _ _ _ b _ : _) -> b
    return (pTs, isVarArity, cti)

  withCurrentTypeMap (\tm -> do
      let key = (tps, pTs, isVA)
      if Map.notMember key (constrs tm)
        then return $ tm { constrs = Map.insert key cti (constrs tm) }
        else failEither $ mkError ConstructorAlreadyDefined sp)
    tcba

-- Locks -- already handled
-- typeCheckSignature st ld@(LockDecl _ ms i mps mprops) tcba = tcba
  --debug $ "typeCheckSignature: " ++ prettyPrint ld
--  lsig <- withErrCtxt ("When checking signature of lock " ++ prettyPrint i ++ ":\n") $ do
--    pol <- getLockPolicy ms
--    return $ VSig (lockT []) pol True True
    -- TODO: Check properties!
--    return $ LSig pol (length mps)
--  withTypeMap (\tm -> tm { locks = Map.insert i lsig (locks tm) }) $
--    tcba

typeCheckSignature _ _ tcba = tcba

withParam ::  (FormalParam SourcePos, TcType, PL.PrgPolicy) -> TcDeclM a -> TcDeclM a
withParam (FormalParam _ ms _ _ (VarId _ i), ty, p) = do
    let vsig = VSig ty (PL.VarPolicy p) True (Static defaultPos `elem` ms) (Final defaultPos `elem` ms) (Notnull defaultPos `elem` ms)
    withCurrentTypeMap $ \tm -> return $ tm { fields = Map.insert (unIdent i) vsig (fields tm) }

withParam (FormalParam _ _ _ _ arvid, _, _) =
    fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid


typeCheckExnSig :: CodeState -> ExceptionSpec SourcePos -> TcDeclM (TcType, ExnSig)
typeCheckExnSig st (ExceptionSpec _ ms xT) = do
  withErrCtxt (FallbackContext ("When checking signature for declared exception " ++ prettyPrint xT)) $ do
    ty <- TcRefT <$> evalSrcRefType genBot xT
    {-- Check that type exists - now done in evalSrcRefType
    mTm <- lookupTypeOfT ty <$> getTypeMap
    case mTm of
      Just _ -> return ()
      Nothing -> fail $ "Unknown exception type: " ++ prettyPrint ty -}
    checkPolicyMods st ms
       "typeCheckSignature: At most one read/write modifier allowed per exception"
    wPol <- getWritePolicy ms
    rPol <- getExnReadPolicy (PL.VarPolicy wPol) ms
    lms  <- checkLMMods ms
    let xSig = ExnSig {
               exnReads = rPol,
               exnWrites = PL.VarPolicy wPol,
               exnMods = lms
             }
    return (ty, xSig)

checkPolicyMods :: CodeState -> [Modifier SourcePos] -> String -> TcDeclM ()
checkPolicyMods st ms failStr = do
  --debug $ "checkPolicyMods: " ++ show ms
  let rPolExps = [ e | Reads  _ e <- ms ]
      wPolExps = [ e | Writes _ e <- ms ]
  check (length rPolExps <= 1 && length wPolExps <= 1) $ toUndef failStr
  mapM_ (typeCheckPolicyMod st) $ rPolExps ++ wPolExps

checkLMMods :: [Modifier SourcePos] -> TcDeclM PL.TcLockDelta
checkLMMods ms = do
  let cs = concat [ l | Closes _ l <- ms ]
      os = concat [ l | Opens  _ l <- ms ]
  tcCs <- map PL.skolemizeLock <$> mapM evalLock cs
  tcOs <- map PL.skolemizeLock <$> mapM evalLock os
  return $ PL.LockDelta tcOs tcCs

checkExpectsMods :: [Modifier SourcePos] -> TcDeclM [PL.TcLock]
checkExpectsMods ms = do
  let es = concat [ l | Expects _ l <- ms ]
  mapM evalLock es

typeCheckParam :: CodeState -> FormalParam SourcePos -> TcDeclM (TcType, B.ByteString, PL.PrgPolicy, Maybe B.ByteString)
typeCheckParam st (FormalParam _ ms t ell (VarId _ i)) = do
  withErrCtxt ( FallbackContext ("When checking signature of parameter " ++ prettyPrint i)) $ do
    -- 1. Check parameter type
    ty <- evalSrcType genBot t
    -- 2. Typecheck and evaluate policy modifier
    checkPolicyMods st ms
       "typeCheckSignature: At most one read modifier allowed per parameter"
    rPol <- getParamPolicy (unIdent i) ms
    let mNN = if Notnull defaultPos `elem` ms then Just $ unIdent i else Nothing
    bt <- PL.bottomM
    return (if ell then arrayType ty bt else ty, unIdent i, rPol, mNN)
typeCheckParam _ (FormalParam _ _ _ _ arvid) =
    fail $ "Deprecated array syntax not supported: " ++ prettyPrint arvid

typeCheckPolicyMod :: CodeState -> Policy SourcePos -> TcDeclM (Policy T)
typeCheckPolicyMod st polExp = do
  -- tm <- getTypeMap
  -- debug $ show tm
  -- debugPrint $ "typeCheckPolicyMod: " ++ prettyPrint polExp
  tp <- PL.topM
  ((ty, _pol, polExp'), cs) <- runTcCodeM (simpleEnv tp True
                                            ("policy modifier " ++ prettyPrint polExp) False) st
                                  (--liftBase (debug "inside runTC") >>
                                   tcExp polExp)
  check (null cs) $ toUndef "Internal WTF: typeCheckPolicyMod: Constraints in policy exp?!?"
  check (isPolicyType ty) $ toUndef $ "Wrong type for policy expression: " ++ prettyPrint ty
  -- check that _pol is bottom shouldn't be necessary
  return polExp'


-- end signatures
------------------------------------------------------------------------------
-- Initializers

-- Precondition: Only init decls
typeCheckInitDecls :: ActorPolicy -> ActorPolicy -> [Decl SourcePos] -> TcDeclM [Decl T]
typeCheckInitDecls sLim cLim is = do
  stSt <- setupStartState
  (sIs, st) <- go (typeCheckInitDecl sLim) stSt [] [ bl | InitDecl _ True  bl <- is ]
  (iIs, _ ) <- go (typeCheckInitDecl cLim) st   [] [ bl | InitDecl _ False bl <- is ]
  return (map (InitDecl Nothing True) sIs ++ map (InitDecl Nothing False) iIs)

      where go :: (CodeState -> Block SourcePos -> TcDeclM (CodeState, Block T))
               -> CodeState -> [Block T] -> [Block SourcePos] -> TcDeclM ([Block T], CodeState)
            go _ st acc [] = return (reverse acc, st)
            go f st acc (bl:bls) = do (st', blT) <- f st bl
                                      go f st' (blT:acc) bls


typeCheckInitDecl :: ActorPolicy -> CodeState -> Block SourcePos -> TcDeclM (CodeState, Block T)
typeCheckInitDecl lim st bl = do
    tm <- getTypeMap
    (newSB,cs) <- runTcCodeM (simpleEnv lim False "initializer block" False) st $
                      addBranchPCList (map (Ident defaultPos) (Map.keys (fields tm))) $ do
                        bl' <- tcBlock bl
                        s <- getState
                        return (s, bl')
    solve cs
    return newSB

------------------------------------------------------------------------------
-- Bodies

typeCheckMemberDecls :: ActorPolicy
                     -> ActorPolicy
                     -> [MemberDecl SourcePos] -> TcDeclM [MemberDecl T]
typeCheckMemberDecls sLim cLim ms = do
  st <- setupStartState
  mapM (typeCheckMemberDecl sLim cLim st) ms

typeCheckMemberDecl :: ActorPolicy -> ActorPolicy -> CodeState -> TypeCheck TcDeclM MemberDecl
typeCheckMemberDecl sLim cLim st fd@FieldDecl{} =
    typeCheckFieldDecl sLim cLim st fd
typeCheckMemberDecl _ _ st md@MethodDecl{} =
    typeCheckMethodDecl st md
typeCheckMemberDecl _ _ st cd@ConstructorDecl{} =
    typeCheckConstrDecl st cd
typeCheckMemberDecl _ _ _ md = return $ notAppl md

typeCheckFieldDecl :: ActorPolicy -> ActorPolicy -> CodeState -> TypeCheck TcDeclM MemberDecl
typeCheckFieldDecl staticLim constrLim st (FieldDecl _ ms _t vds) = do
  --debug $ "typeCheckFieldDecl:" ++ show fd
  let lim = if Static defaultPos `elem` ms then staticLim else constrLim
  vds' <- mapM (typeCheckVarDecl lim st) vds
  return $ FieldDecl Nothing (map notAppl ms) (notAppl _t) vds'

typeCheckFieldDecl _ _ _ md = panic (typeCheckerBase ++ ".typeCheckFieldDecl") $
                              "Applied to non-field decl " ++ show md

typeCheckVarDecl :: ActorPolicy -> CodeState -> TypeCheck TcDeclM VarDecl
typeCheckVarDecl lim st vd@(VarDecl _ (VarId _ i) mInit) = do
  --debug $ "typeCheckVarDecl:" ++ show i
  withErrCtxt (FallbackContext ("When checking initializer of field " ++ prettyPrint i)) $ do
  debugPrint $ "typeCheckVarDecl: " ++ prettyPrint i ++ " : " ++ maybe "" prettyPrint mInit
  tm <- getTypeMap
  debugPrint $ prettyPrint tm
  Just (VSig fieldTy fieldPol _ fieldStatic _ _) <- Map.lookup (unIdent i) . fields <$> getTypeMap
  case mInit of
    Nothing -> return $ notAppl vd
    Just (InitExp _ e) -> do
      (e',cs) <- runTcCodeM (simpleEnv lim False
                              ("field initializer " ++ prettyPrint e) fieldStatic) st $ do
                   (rhsTy, rhsPol, e') <- tcExp e
                   mps <- fieldTy =<: rhsTy
                   case mps of
                     Nothing -> fail "typeCheckVarDecl: type mismatch"
                     Just ps -> do
                        mapM_ (\(p,q) -> do
                                 constraint PL.emptyLockSet p q $ toUndef "Cannot unify policy type parameters at method call"
                                 constraint PL.emptyLockSet q p $ toUndef "Cannot unify policy type parameters at method call") ps
                        constraint PL.emptyLockSet rhsPol fieldPol $ toUndef $
                                       "Cannot assign result of expression " ++ prettyPrint e ++
                                       " with policy " ++ prettyPrint rhsPol ++
                                       " to location " ++ prettyPrint i ++
                                       " with policy " ++ prettyPrint fieldPol
                        return e'
      solve cs
      return $ VarDecl Nothing (VarId Nothing $ notAppl i) $ Just $ InitExp Nothing e'
    Just (InitArray _ arr) ->
      case mArrayType fieldTy of
        Nothing -> fail $ "Field " ++ prettyPrint i
                        ++ " of non-array type " ++ prettyPrint fieldTy
                        ++ " given literal array initializer"
        Just (baseTy, pols) -> do
         (arr',cs) <- runTcCodeM (simpleEnv lim False
                                   ("array initializer " ++ prettyPrint arr) fieldStatic) st $
                         tcArrayInit baseTy pols arr
         solve cs
         return $ VarDecl Nothing (VarId Nothing $ notAppl i) $ Just $ InitArray Nothing arr'
    _ -> panic "" $ show mInit

typeCheckVarDecl _ _ vd = fail $ "Deprecated array syntax not supported: " ++ prettyPrint vd


typeCheckMethodDecl :: CodeState -> TypeCheck TcDeclM MemberDecl
typeCheckMethodDecl st (MethodDecl _ ms tps _rt i ps _exs mb) = do
  -- Lookup the correct function signature
  debugPrint $ "Type-checking method " ++ prettyPrint
                 (MethodDecl defaultPos ms tps _rt i ps _exs (MethodBody defaultPos Nothing))
  withErrCtxt (MethodContext (prettyPrint i)) $ do
  withFoldMap withTypeParam tps $ do
  tysPs <- mapM (evalSrcType genBot) [ t | FormalParam _ _ t _ _ <- ps ]
  let isVarArity = case reverse ps of
                     [] -> False
                     (FormalParam _ _ _ b _ : _) -> b
  Just (MSig tyRet _ pRet pIs pPars pWri expLs lMods xSigs nnps _isN) <- do
      mMap <- fromJust . Map.lookup (unIdent i) . methods <$> getTypeMap
      return $ Map.lookup (tps, tysPs, isVarArity) mMap

  checkParams ps

  --debugPrint $ "pRet: " ++ show pRet
  -- Setup the environment in which to check the body
  let parMods  = [ (iP, ms') | (FormalParam _ ms' _ _ (VarId _ iP)) <- ps ]
      parVsigs = [ (unIdent iP, VSig t _pol {-(ofPol iP)-} True False (isFinal ms') False) |
                    ((iP, ms'), t, _pol) <- zip3 parMods tysPs pPars ]
      pBs  = zip pIs pPars
      pars = map fst parVsigs
      exnPols = map (second $
                     \es -> (exnReads es, exnWrites es)) xSigs
      exnLMods = map (second exnMods) xSigs
      parEnts = [ (VarEntity $ mkSimpleName EName (Ident defaultPos iP), []) | iP <- pars ]
      exnEnts = [ (ExnEntity t, []) | t <- map fst xSigs ]
      branchMap = Map.insert returnE [] $ Map.fromList (parEnts ++ exnEnts)
      writeErr = "body of method " ++ prettyPrint i
      env = CodeEnv {
              vars = [Map.fromList parVsigs],
              lockstate = PL.LockSet $ map PL.skolemizeLock expLs,
              returnI = Just (tyRet, pRet),
              exnsE = Map.fromList exnPols,
              branchPCE = (branchMap, [(pWri, writeErr)]),
              parBounds = pBs,
              compileTime = False,
              staticContext = isMethodStatic ms
            }

  -- debug $ "Using env: " ++ show env
  -- Setup the state in which to check the body
  -- parAids <- concat <$> mapM unknownIfActor (zip pars tysPs)
  --let parAMap = Map.fromList $ map (id *** (\aid -> AI True aid)) parAids
  --    parSt = st { varMapSt = emptyVM { actorSt = parAMap } }

  -- This little thing is what actually checks the body
  ((mb', endSt),cs) <- runTcCodeM env st $ do
                         let nt = zip (map (Ident defaultPos) pIs) tysPs
                         mapM_ (uncurry registerParamType) nt
                         mapM_ (\(pid,t) -> do
                                  st' <- getStateType (Just (mkSimpleName EName pid)) Nothing t
                                  updateStateType (Just (mkSimpleName EName pid, True)) t
                                                      (Just (setNullInStateType st' (NotNull, Free))) )
                                            [(pid, t)| pid <- map (Ident defaultPos) nnps, (pj,t) <- nt, pid==pj]
                         mb' <- tcMethodBody mb
                         checkReturnStmts mb
                         eSt <- getState
                         return (mb', eSt)
  -- ... and then we need to check the end result
  solve cs
  check (lMods `PL.models` lockMods endSt) $ toUndef $
              "Declared lock modifiers not general enough: " ++ show lMods
  mapM_ (checkExnMods endSt) exnLMods
  return $ MethodDecl Nothing (map notAppl ms) (map notAppl tps)
             (notAppl _rt) (notAppl i) (map notAppl ps) (map notAppl _exs) mb'

typeCheckMethodDecl _ md = panic (typeCheckerBase ++ ".typeCheckMethodDecl") $
                            "Applied to non-method decl " ++ show md


typeCheckConstrDecl :: CodeState -> TypeCheck TcDeclM MemberDecl
typeCheckConstrDecl st (ConstructorDecl _ ms tps ci ps _exs cb) = do
  withErrCtxt (ConstructorBodyContext (prettyPrint ci)) $ do
  --debug $ "Type-checking constructor:\n " ++ prettyPrint cd
  withFoldMap withTypeParam tps $ do
  -- Lookup the correct function signature
  tysPs <- mapM (evalSrcType genBot) [ t | FormalParam _ _ t _ _ <- ps ]
  let isVarArity = case reverse ps of
                     [] -> False
                     (FormalParam _ _ _ b _ : _) -> b
  Just (CSig pIs pPars pWri expLs lMods xSigs nnps _isN) <-
      Map.lookup (tps, tysPs, isVarArity) . constrs <$> getTypeMap

  checkParams ps

  -- Setup the environment in which to check the body
  tm <- getTypeMap
  tp <- PL.topM
  let parVsigs = [ (unIdent i, VSig t _pol {-(ofPol i)-} True False (isFinal ms') False) |
                    (FormalParam _ ms' _ _ (VarId _ i), t, _pol) <- zip3 ps tysPs pPars ]
      pars = map fst parVsigs
      pBs  = zip pars pPars
      exnPols = map (second $
                     \es -> (exnReads es, exnWrites es)) xSigs
      exnLMods = map (second exnMods) xSigs
      parEnts = [ VarEntity $ mkSimpleName EName (Ident defaultPos i) | i <- pars ]
      exnEnts = [ ExnEntity t | t <- map fst xSigs ]
      -- Assigning to non-static fields of 'this' in a constructor is a local write
      fieEnts = concat [ [ThisFieldEntity i,VarEntity (mkSimpleName EName (Ident defaultPos i))]
                             | (i, VSig _ _ _ False _ _) <- Map.assocs (fields tm) ]
  --debug $ "fieEnts: " ++ show fieEnts
  let branchMap = Map.fromList $ zip (parEnts ++ exnEnts ++ fieEnts) (repeat [])
      writeErr = "body of constructor " ++ prettyPrint ci
      env = CodeEnv {
              vars = [Map.fromList parVsigs],
              lockstate = PL.LockSet $ map PL.skolemizeLock expLs,
              returnI = Just (voidT, tp),
              exnsE = Map.fromList exnPols,
              branchPCE = (branchMap, [(pWri, writeErr)]),
              parBounds = pBs,
              compileTime = False,
              staticContext = isMethodStatic ms
            }

  --debug $ "Using branch map: " ++ show (branchPCE env)
  -- Setup the state in which to check the body
--  parAids <- concat <$> mapM unknownIfActor (zip pars tysPs)
--  let parAMap = Map.fromList $ map (mkSimpleName EName *** (\aid -> AI aid Stable)) parAids
--      parSt = st { actorSt = parAMap `Map.union` actorSt st }

  -- This little thing is what actually checks the body
  ((cb',endSt),cs) <- runTcCodeM env st $ do
                        let nt = zip (map (Ident defaultPos) pIs) tysPs
                        mapM_ (uncurry registerParamType) nt
                        mapM_ (\(i,t) -> do
                                 st' <- getStateType (Just (mkSimpleName EName i)) Nothing t
                                 updateStateType (Just (mkSimpleName EName i, True)) t (Just (setNullInStateType st' (NotNull, Free))) )
                          [(i, t) | i <- map (Ident defaultPos) nnps, (j,t) <- nt, i==j]
                        cb' <- tcConstrBody cb
                        eSt <- getState
                        return (cb', eSt)

  -- ... and then we need to check the end result
  let nnfs = [i | (i, VSig _ _ _ _ _ True) <- Map.assocs (fields tm)]
      iSt = instanceSt $ varMapSt endSt
  mapM_ (\nnf -> check (case Map.lookup nnf iSt of
                          Just ii | not $ nullable (iNull ii) -> True
                          _ -> False) $ toUndef $ "The field " ++ prettyPrint nnf ++ " is required to be initialized.") nnfs
  solve cs
  check (lMods `PL.models` lockMods endSt) $ toUndef $
              "Declared lock modifiers not general enough: " ++ show lMods
  mapM_ (checkExnMods endSt) exnLMods
  return $ ConstructorDecl Nothing (map notAppl ms) (map notAppl tps) (notAppl ci)
             (map notAppl ps) (map notAppl _exs) cb'

typeCheckConstrDecl _ md = panic (typeCheckerBase ++ ".typeCheckConstrDecl") $
                            "Applied to non-constructor decl " ++ show md

{-
unknownIfActor :: (Ident (), TcType) -> TcDeclM [(Ident (), ActorId)]
unknownIfActor (i, ty)
    | ty == actorT = unknownActorId >>= \aid -> return [(i, aid)]
    | otherwise = return []
-}
{-
ofPol :: Ident SourcePos -> ActorPolicy
ofPol = PL.VarPolicy . TcRigidVar True . unIdent
-}

checkExnMods :: CodeState -> (TcType, PL.LockMods) -> TcDeclM ()
checkExnMods st (xTy, lms) = do
  let mExnSt = epState <$> Map.lookup (ExnType xTy) (exnS st)
  maybeM mExnSt $ \sX -> do
    check (lms `PL.models` lockMods sX) $ toUndef $
              "Declared exception lock modifiers not general enough: "
              ++ show lms
{-
getParamBound :: ActorPolicy -> PrgPolicy TcActor
getParamBound (PL.VarPolicy (TcRigidVar _)) = top
getParamBound (PL.VarPolicy p) = p
getParamBound _ = top
-}

tcMethodBody :: TypeCheck TcCodeM MethodBody
tcMethodBody (MethodBody _ mBlock) =
    MethodBody Nothing <$> maybe (return Nothing) ((Just <$>) . tcBlock) mBlock

tcConstrBody :: TypeCheck TcCodeM ConstructorBody
tcConstrBody (ConstructorBody _ mEci stmts) = do
  mEci' <- maybe (return Nothing) ((Just <$>) . tcEci) mEci
  stmts' <- tcBlockStmts stmts
  return $ ConstructorBody Nothing mEci' stmts'
--tcConstrBody (ConstructorBody _ Just eci) _) = tc
--    = fail $ "Explicit constructor invocation not yet supported: " ++ prettyPrint eci










{------------------------------------------
-- The stuff down here should likely live somewhere else

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
skolemParam tp = case tp of
                   TypeParam _ i _    ->
                       TcActualType (TcClsRefT (TcClassT (mkSimpleName TName i) []))
                   ActorParam  _ i    -> TcActualActor (ActorTPVar $ unIdent i)
                   PolicyParam _ i    -> TcActualPolicy (PL.VarPolicy $ TcRigidVar False $ unIdent i)
                   LockStateParam _ i -> TcActualLockState [TcLockVar $ unIdent i]

-}

isPolicyMod, isLockStateMod :: Modifier SourcePos -> Bool
isPolicyMod m =
    case m of
      Reads _ _ -> True
      Writes _ _ -> True
      _ -> False
isLockStateMod m =
    case m of
      Expects _ _ -> True
      Opens   _ _ -> True
      Closes  _ _ -> True
      _ -> False


solve :: [PL.ConstraintWMsg] -> TcDeclM ()
solve cs = do
  finePrint $ "Solving (" ++ show (length cs) ++ ") constraints... "
  debugPrint "Constraints:\n"
  mapM_ (debugPrint . show) cs
  checkM (PL.solve $ map fst cs) $
         toUndef "The system failed to infer the set of unspecified policies"
  finePrint "... Done!"

-- | Checks for redeclaration of parameters
checkParams :: [FormalParam SourcePos] -> TcDeclM ()
checkParams ps = do
  (foldM_ (\argSet param ->
          let parIdStr = unIdent $ getFormalParamId param
          in  if Set.member parIdStr argSet
                then failE $
                  mkError (ParameterAlreadyDefined (B.unpack parIdStr)) (ann param)
                else return $ Set.insert parIdStr argSet)
          Set.empty ps)

