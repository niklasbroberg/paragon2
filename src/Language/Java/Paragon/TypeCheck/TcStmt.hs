{-# LANGUAGE TupleSections, BangPatterns #-}
module Language.Java.Paragon.TypeCheck.TcStmt where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.Error
import Language.Java.Paragon.SourcePos

import qualified Language.Java.Paragon.PolicyLang as PL
import Language.Java.Paragon.TypeCheck.Monad
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.TypeMap

import Language.Java.Paragon.TypeCheck.TcExp

import Control.Monad (unless, void)
import Control.Applicative ((<$>))

import qualified Data.ByteString.Char8 as B

tcStmtModule :: String
tcStmtModule = typeCheckerBase ++ ".TcStmt"

-----------------------------------
--    Typechecking Statements    --
-----------------------------------

tcStmt :: TypeCheck TcCodeM Stmt

-- Rule EMPTY
tcStmt (Empty _) = return $ Empty Nothing

-- Rule EXPSTMT
tcStmt (ExpStmt _ e) = do
  (_,_,e') <- tcExp e
  return $ ExpStmt Nothing e'

-- Rule BLOCK
tcStmt (StmtBlock _ b) = StmtBlock Nothing <$> tcBlock b

-- Rule IF
tcStmt (IfThenElse _ c s1 s2) = do
  (tyC, pC, c') <- tcExp c
  --check (tyC `elem` [booleanT, clsTypeToType . fromJust . box $ BooleanT ()])
  check (isBoolConvertible tyC)
             $  toUndef $ "if-statement requires a condition of type compatible with boolean\n"
               ++ "Found type: " ++ prettyPrint tyC
  extendBranchPC pC ("branch dependent on condition " ++ prettyPrint c) $ do
    (s1', s2') <- (isNotNullChecked c
                    >> maybeM (mLocks tyC) (applyLockMods . PL.openAll . map PL.skolemizeLock)
                    >> tcStmt s1)
                  ||| (isNullChecked c >> tcStmt s2)
    return $ IfThenElse Nothing c' s1' s2'

-- Rule IFTHEN
tcStmt (IfThen sp c s) = do
  IfThenElse no c' s' _ <- tcStmt (IfThenElse sp c s (Empty sp))
  return (IfThen no c' s')

-- Rule WHILE
tcStmt (While _ c sBody) = do
  !s <- getState                  -- Starting state S
  (tyC, pC, c') <- tcExp c
  check (isBoolConvertible tyC) $ toUndef "Cannot convert type to boolean"
  extendBranchPC pC ("loop over condition " ++ prettyPrint c) $
    addBranchPC breakE $
    addBranchPC continueE $
     do maybeM (mLocks tyC)
         (applyLockMods . PL.openAll . map PL.skolemizeLock)
        -- First iteration of body
        sBody' <- isNotNullChecked c >> tcStmt sBody

        -- Approximate state to the possible ones
        -- at the start of the loop
        sCont <- getExnState ExnContinue -- TODO smart constructor
        maybeM sCont mergeWithState
        mergeWithState s             -- S* = S <> Ss <> Ss[exns](continue)[state]
        deactivateExn ExnContinue    -- S** = S*[exns /= continue]

{- Commenting out due to lock state -- don't change the lockstate in a loop!
        -- Second iteration of condition
        _ <- tcExp c -- This is only to get the (potentially) more difficult constraints
        maybeM (mLocks tyC) (\ls -> applyLockMods ([],ls))

        -- Second iteration of body
        _ <- tcStmt sBody -- Again for the sake of the constraints, and outgoing state
-}
        -- Fix outgoing state
        sBreak <- getExnState ExnBreak   -- Sb = Ss'[exns](break)[state]
        maybeM sBreak mergeWithState     -- S' = Se' <> Sb
        deactivateExn ExnBreak           -- S'' = S'[exns /= break]
        return $ While Nothing c' sBody'

-- Rule BASICFOR
tcStmt (BasicFor _ mForInit mTest mUp body) = do
  (mForInit', forf) <- withInits mForInit $ do
    !s <- getState
    (tyC, pC, mTest') <- case mTest of
                           Nothing -> PL.bottomM >>= \bt ->
                                        return (stateType booleanT, bt, Nothing)
                           Just test -> do
                              (ty, p, test') <- tcExp test
                              return (ty, p, Just test')
    check (isBoolConvertible tyC) $  toUndef $
              "Test in basic for loop must have a bool-convertible type. \n" ++
              "Found type: " ++ prettyPrint tyC
    maybe id (\test -> extendBranchPC pC
                       ("for loop dependent on condition " ++ prettyPrint test)) mTest $
      addBranchPC breakE $
      addBranchPC continueE $ do
        maybeM (mLocks tyC)
         (applyLockMods . PL.openAll . map PL.skolemizeLock)
        -- First iteration of body
        body' <- tcStmt body
        mUp' <- case mUp of
                  Nothing -> return Nothing
                  Just up -> do (_,_,up') <- unzip3 <$> mapM tcExp up
                                return $ Just up'

        -- Approximate state to the possible ones
        -- at the start of the loop
        sCont <- getExnState ExnContinue -- TODO smart constructor
        maybeM sCont mergeWithState
        mergeWithState s             -- S* = S <> Ss <> Ss[exns](continue)[state]
        deactivateExn ExnContinue    -- S** = S*[exns /= continue]

{- Commenting out due to space leak -- don't change the lock state in a loop!
        -- Second iteration of condition
        _ <- maybe (return undefined) tcExp mTest -- This is only to get the (potentially) more difficult constraints
        maybeM (mLocks tyC) (\ls -> applyLockMods ([],ls))

        -- Second iteration of body
        _ <- tcStmt body -- Again for the sake of the constraints, and outgoing state
        _ <- maybe (return undefined) (mapM tcExp) mUp
-}
        -- Fix outgoing state
        sBreak <- getExnState ExnBreak   -- Sb = Ss'[exns](break)[state]
        maybeM sBreak mergeWithState     -- S' = Se' <> Sb
        deactivateExn ExnBreak           -- S'' = S'[exns /= break]
        return $ \mForInit' -> BasicFor Nothing mForInit' mTest' mUp' body'
  return $ forf mForInit'

-- Rule BREAK
tcStmt (Break _ Nothing) = do
  pc <- getCurrentPC breakE
  throwExn ExnBreak pc
  return $ Break Nothing Nothing

-- Rule CONTINUE
tcStmt (Continue _ Nothing) = do
  pc <- getCurrentPC continueE
  throwExn ExnContinue pc
  return $ Continue Nothing Nothing

-- Rule RETURNVOID
tcStmt (Return _ Nothing) = do
  (tyR, _pR) <- getReturn
  check (tyR == voidT) $ toUndef "Encountered unexpected empty return statement"
{-  check (pR == top)   $ "Internal error: tcStmt: "
                          ++ "void return with non-top return policy should never happen: " ++ show pR
-}
  pc <- getCurrentPC returnE
  throwExn ExnReturn pc
  return $ Return Nothing Nothing

-- Rule RETURN
tcStmt (Return _ (Just e)) = do
  (tyR, pR) <- getReturn
  (tyE, pE, e') <- tcExp e
  mps <- tyR =<: tyE
  case mps of
    Nothing -> fail $ "Returned value has wrong type: " ++ prettyPrint tyE ++ "\n" ++
                             "Expecting type: " ++ prettyPrint tyR
    Just ps -> do
      mapM_ (\(p,q) -> do
               constraint PL.emptyLockSet p q $ toUndef "Cannot unify policy type parameters at method call"
               constraint PL.emptyLockSet q p $ toUndef "Cannot unify policy type parameters at method call") ps

      -- Check pE <=[L] pR
      constraintLS pE pR $ toUndef $
               "Returned value has too restrictive policy:\n" ++
               "Return expression: " ++ prettyPrint e ++ "\n" ++
               "  with policy: " ++ prettyPrint pE ++ "\n" ++
               "Declared policy bound: " ++ prettyPrint pR
      -- Check E[branchPC](return) <= pR
      bpcs <- getBranchPC returnE
      constraintPC bpcs pR $ \p src -> toUndef $
          "Returning from method, visible at policy " ++ prettyPrint pR ++
               ", not allowed in " ++ src ++
               " with write effect bound " ++ prettyPrint p
      -- Check exnPC(S) <= pR
      epc <- getExnPC
      constraintPC epc pR $ \p src -> toUndef $
          "Returning from method, visible at policy " ++ prettyPrint pR ++
               ", not allowed in " ++ src ++
               " with write effect bound " ++ prettyPrint p
      throwExn ExnReturn pR
      return $ Return Nothing (Just e')

-- Rule THROW
tcStmt (Throw _ eX) = do
  (styX, pX, eX') <- tcExp eX
  let tyX = unStateType styX
  -- TODO: check (tyX <: "Throwable")
  (rX, wX) <- lookupExn tyX
  -- Check E[branchPC](X) <= E[exns](X)[write]
  bpc <- getBranchPC (exnE tyX)
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
  -- Check pX <=[L] E[exns](X)[read]
  constraintLS pX rX $ toUndef $
               "Thrown value has too restrictive policy:\n" ++
               "Expression thrown: " ++ prettyPrint eX ++ "\n" ++
               "  of type: " ++ prettyPrint tyX ++ "\n" ++
               "  with policy: " ++ prettyPrint pX ++ "\n" ++
               "Declared exception policy: " ++ prettyPrint rX
  throwExn (ExnType tyX) wX
  return $ Throw Nothing eX'

-- Rule TRYCATCH
tcStmt (Try _ block [catch] Nothing) = do
  let Catch sp (FormalParam _ ms t False (VarId _ i)) cBlock = catch
  debugPrint $ "## Catching: " ++ prettyPrint t
  (tyP, tT) <- tcSrcType genMeta t
  deactivateExn (ExnType tyP)
  registerParamType i tyP
  -- TODO check tyP <: "Throwable"
  pW <- newMetaPolVar (Ident sp (B.pack $ prettyPrint t))
                                    -- \pi, where \pi is fresh
  pR <- liftTcDeclM $ getExnReadPolicy pW ms -- getParamPolicy i ms
  addBranchPC (exnE tyP) $          -- E' = E[branchPC{tyP +-> bottom},
    registerExn tyP pR pW $ do      --        exns{tyP +-> (pR, \pi)}]
      block' <- tcBlock block
      extendVarEnv (unIdent i) (VSig tyP pR True False (isFinal ms) False) $ do --Last bool uncertain
                                         -- E* = E[vars{x +-> (tyP, pR)}]
        msX <- getExnState (ExnType tyP)
        debugPrint $ "msX: " ++ show (void msX)
        maybeM msX mergeWithState  -- S* = St <> St[exns](X)[state]
        cBlock' <- tcBlock cBlock
        deactivateExn (ExnType tyP)
        let catch' = Catch Nothing (FormalParam Nothing (map notAppl ms)
                                    tT False (VarId Nothing (notAppl i))) cBlock'
        return $ Try Nothing block' [catch'] Nothing

-- Rule TRYFINALLY
tcStmt (Try _ block [] (Just finBlock)) = do
  sS <- getState     -- Must store starting state for later
  block' <- tcBlock block
  -- TODO: we actually merge with "too many" states here -- unfortunate, but conservative
  mergeActiveExnStates  -- S* = St <> <>{ Sx | X <- dom(St[exns]), St[exns](X)[state] = Sx }
  sStar <- getState
  useExnState sS        -- S** = S*[exns = S[exns]]
  finBlock' <- tcBlock finBlock
  sF <- getState
  useExnState sStar     -- S' = Sf[exns = S*[exns]]
  mergeWithState sF     --       <> Sf
  return $ Try Nothing block' [] (Just finBlock')

-- Pre-process TRYCATCH/TRYFINALLY
tcStmt (Try sp blk catches mFinally) = do
    let catchChain = linearise catches mFinally blk
    tcStmt catchChain
        where linearise :: [Catch SourcePos] -> Maybe (Block SourcePos) -> Block SourcePos -> Stmt SourcePos
              linearise [] justFin  block = Try sp block [] justFin
              linearise [c] Nothing block = Try sp block [c] Nothing
              linearise (c:cs) mFin block = linearise cs mFin $ bl (Try sp block [c] Nothing)
              bl :: Stmt SourcePos -> Block SourcePos
              bl = Block sp . return . BlockStmt sp

-- Rule OPEN
-- TODO change the list of actor names to a list of expressions (parser, AST, here)
tcStmt os@(Open _ (Lock sp n@(Name _ nt mPre i) as)) = do
  unless (nt == LName) $
         panic (tcStmtModule ++ ".tcStmt:Open")
                   $ "Unexpected name: " ++ show n
  LSig pL lTys _ <- lookupLock mPre i
  -- (_,pL) <- lookupVar n
  check (length as == length lTys) $
            mkError (LArityMismatch (prettyPrint n) (length lTys) (length as)) sp
  -- Check pI <=[L] pL
  psAs <- map snd <$> mapM lookupActorName as
  mapM_ (\(a,pA) -> constraintLS pA pL $ toUndef $
                      "Lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
                      " cannot be opened for actor " ++ prettyPrint a ++
                      " with policy " ++ prettyPrint pA
        ) (zip as psAs)
  -- Check E[branchPC](L) <= pL
  bpc <- getBranchPC (lockE n)
  constraintPC bpc pL $ \p src -> toUndef $
      "Opening lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
      " not allowed in " ++ src ++
      " with write effect bound " ++ prettyPrint p
  -- Check exnPC(S) <= pL
  epc <- getExnPC
  constraintPC epc pL $ \p src -> toUndef $
      "Opening lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
      " not allowed in " ++ src ++
      " with write effect bound " ++ prettyPrint p

  debugPrint $ "\ntcStmt[Open]: Checking actor ids: " ++ show as
  aids <- mapM tcActorName as
  let tysArgs = map PL.actorType aids
  mapM_ (\(rTy, rTyArg) ->
             checkM (rTyArg `subTypeOf` rTy) $
                    toUndef $ "Lock " ++ prettyPrint n ++ " expects argument of type " ++
                            prettyPrint rTy ++ " but has been given argument of type " ++
                            prettyPrint rTyArg)
            $ zip lTys tysArgs
  openLock $ PL.ConcreteLock $ PL.Lock n aids
  return $ notAppl os

-- Rule CLOSE
tcStmt cs@(Close _ (Lock _ n@(Name _ nt mPre i) as)) = do
  unless (nt == LName) $
         panic (tcStmtModule ++ ".tcStmt:Close")
                   $ "Unexpected name: " ++ show n
  LSig pL lTys _ <- lookupLock mPre i
--  (_,pL) <- lookupVar n
--  LTI arL pL <- lookupLock n
  check (length as == length lTys) $  toUndef $
            "Lock " ++ prettyPrint n ++ " expects " ++ show (length lTys)
                    ++ " arguments but has been given " ++ show (length as)
  -- Check pI <=[L] pL
  psAs <- map snd <$> mapM lookupActorName as
  mapM_ (\(arg,argP) -> constraintLS argP pL $ toUndef $
                      "Lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
                      " cannot be closed for actor " ++ prettyPrint arg ++
                      " with policy " ++ prettyPrint argP
        ) (zip as psAs)
  -- Check E[branchPC](L) <= pL
  bpc <- getBranchPC (lockE n)
  constraintPC bpc pL $ \p src -> toUndef $
      "Closing lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
      " not allowed in " ++ src ++
      " with write effect bound " ++ prettyPrint p
  -- Check exnPC(S) <= pL
  epc <- getExnPC
  constraintPC epc pL $ \p src -> toUndef $
      "Closing lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
      " not allowed in " ++ src ++
      " with write effect bound " ++ prettyPrint p

  debugPrint $ "\ntcStmt[Close]: Checking actor ids: " ++ show as
  aids <- mapM tcActorName as
  let tysArgs = map PL.actorType aids
  mapM_ (\(rTy, rTyArg) ->
             checkM (rTyArg `subTypeOf` rTy) $
                    toUndef $ "Lock " ++ prettyPrint n ++ " expects argument of type " ++
                            prettyPrint rTy ++ " but has been given argument of type " ++
                            prettyPrint rTyArg)
            $ zip lTys tysArgs
  closeLock $ PL.ConcreteLock $ PL.Lock n aids
  return $ notAppl cs

-- Rule OPENIN
tcStmt (OpenBlock _ l@(Lock _ n@(Name _ nt mPre i) as) block) = do
  unless (nt == LName) $
         panic (tcStmtModule ++ ".tcStmt:OpenBlock")
                   $ "Unexpected name: " ++ show n
  LSig pL lTys _ <- lookupLock mPre i
  -- (_,pL) <- lookupVar n
  --debugTc $ "pL: " ++ prettyPrint n ++ ": " ++ show pL
  check (length as == length lTys) $  toUndef $
            "Lock " ++ prettyPrint n ++ " expects " ++ show (length lTys)
                    ++ " arguments but has been given " ++ show (length as)
  -- Check pI <=[L] pL
  psAs <- map snd <$> mapM lookupActorName as
  --debugTc $ "psAs: " ++ show psAs
  mapM_ (\(arg,argP) -> constraintLS argP pL $ toUndef $
                      "Lock " ++ prettyPrint n ++ " with policy " ++ prettyPrint pL ++
                      " cannot be opened for actor " ++ prettyPrint arg ++
                      " with policy " ++ prettyPrint argP
        ) (zip as psAs)

  debugPrint $ "\ntcStmt[OpenBlock]: Checking actor ids: " ++ show as
  aids <- mapM tcActorName as
  let tysArgs = map PL.actorType aids
  mapM_ (\(rTy, rTyArg) ->
             checkM (rTyArg `subTypeOf` rTy) $
                    toUndef $ "Lock " ++ prettyPrint n ++ " expects argument of type " ++
                            prettyPrint rTy ++ " but has been given argument of type " ++
                            prettyPrint rTyArg)
            $ zip lTys tysArgs
  extendLockEnv [PL.ConcreteLock $ PL.Lock n aids] $
    OpenBlock Nothing (notAppl l) <$> tcBlock block


tcStmt s = fail $ "Unsupported statement: " ++ prettyPrint s


withInits :: Maybe (ForInit SourcePos) -> TcCodeM a -> TcCodeM (Maybe (ForInit T), a)
withInits Nothing tca = (Nothing,) <$> tca
withInits (Just (ForInitExps _ es)) tca = do
    (_,_,es') <- unzip3 <$> mapM tcExp es
    (Just $ ForInitExps Nothing es',) <$> tca
withInits (Just (ForLocalVars _ ms t vds)) tca = do
  pV  <- localVarPol ms vds
  (tyV, tT) <- tcSrcType genMeta t
  (vds', a) <- tcLocalVars pV tyV (isFinal ms) vds [] tca
  return (Just $ ForLocalVars Nothing (map notAppl ms) tT vds', a)


----------------------------------------
-- Typechecking Blocks and BlockStmts --
----------------------------------------

tcBlock :: TypeCheck TcCodeM Block
tcBlock (Block _ bss) = Block Nothing <$> insideBlock (tcBlockStmts bss)

insideBlock :: TcCodeM a -> TcCodeM a
insideBlock = withEnv (\env -> return $ env { vars = emptyVarMap : vars env })

tcBlockStmts :: [BlockStmt SourcePos] -> TcCodeM [BlockStmt T]
-- Rule EMPTYBLOCK
tcBlockStmts [] = return []

-- Rule BLOCKSTMT
tcBlockStmts (BlockStmt _ stmt : bss) = do
  stmt' <- tcStmt stmt
  bss'  <- tcBlockStmts bss
  return (BlockStmt Nothing stmt':bss')

-- Rule LOCALVARINIT/LOCALVARDECL
tcBlockStmts (LocalVars _ ms t vds : bss) = do
  let rPolExps = [ e | Reads _ e <- ms ]
  check (length rPolExps <= 1) $ toUndef
              "At most one read modifier allowed per variable"
--  mapM_ tcPolicyMod rPolExps
  pV  <- localVarPol ms vds
  (tyV, tT) <- tcSrcType genMeta t
--  debugTc $ "Array type pre: " ++ prettyPrint t
  (vds', bss') <- tcLocalVars pV tyV (isFinal ms) vds [] $
                    tcBlockStmts bss
  return (LocalVars Nothing (map notAppl ms) tT vds' : bss')

tcBlockStmts (b:_bss) = fail $ "Unsupported block statement: " ++ prettyPrint b

{-
tcPolicyMod :: Error e => Policy () -> TcCodeM (Policy T)
tcPolicyMod polExp = do
  (ty, _pol, polExp') <- tcExp polExp
  check (isPolicyType ty) $ toUndef $ "Wrong type for policy expression: " ++ prettyPrint ty
  return polExp'
-}

tcLocalVars ::  PL.ActorPolicy -> TcType -> Bool -> [VarDecl SourcePos]
            -> [VarDecl T] -> TcCodeM a -> TcCodeM ([VarDecl T], a)
tcLocalVars _ _ _ [] acc cont = cont >>= \a -> return (reverse acc, a)


-- Rule LOCALVARDECL
tcLocalVars pV tyV fin (vd@(VarDecl _ (VarId _ i) Nothing):vds) acc cont = do
  debugPrint $ "\n####    " ++ prettyPrint vd ++ "    ####\n"
  _styV <- registerStateType i tyV True Nothing
  extendVarEnv (unIdent i) (VSig tyV pV False False fin False) $ do
  addBranchPC (varE (mkSimpleName EName i)) $ do
    tcLocalVars pV tyV fin vds (notAppl vd : acc) cont

-- Rule LOCALVARINIT (Exp)
tcLocalVars pV tyV fin (vd0@(VarDecl _sp (VarId _ i) (Just (InitExp spE e))):vds) acc cont = do
  debugPrint $ "\n####    " ++ prettyPrint vd0 ++ "    ####\n"
  (tyE, pE, e') <- tcExp e
  mps <- tyV =<: tyE
  case mps of
    Nothing -> fail $ "Type mismatch: " ++ prettyPrint (unStateType tyE) ++
                                   " <=> " ++ prettyPrint tyV
    Just ps -> do
      mapM_ (\(p,q) -> do
               constraint PL.emptyLockSet p q (toUndef "Cannot unify policy type parameters at method call")
               constraint PL.emptyLockSet q p (toUndef "Cannot unify policy type parameters at method call")) ps

      constraintLS pE pV $ mkError
        (PolViolatedAss (prettyPrint e) (prettyPrint pE)
                        (prettyPrint i) (prettyPrint pV)) spE

      _styV <- registerStateType i tyV True (Just tyE)

      extendVarEnv (unIdent i) (VSig tyV pV False False fin False) $ do
       addBranchPC (varE (mkSimpleName EName i)) $ do
        --debugPrint $ "Done with local var init"
        let vd = VarDecl Nothing (VarId Nothing $ notAppl i) (Just (InitExp Nothing e'))
        tcLocalVars pV tyV fin vds (vd:acc) cont

-- Rule LOCALVARINIT (Array)
tcLocalVars pV tyV fin (VarDecl _ (VarId _ i) (Just (InitArray _ arr)):vds) acc cont = do
  case mArrayType tyV of
    Just (tyA, pAs) -> do
--      debugTc $ "Array type post: " ++ prettyPrint tyV
      arr' <- tcArrayInit tyA pAs arr
      _styV <- registerStateType i tyV True (Just $ stateType tyV)
      extendVarEnv (unIdent i) (VSig tyV pV False False fin False) $ do
        let vd = VarDecl Nothing (VarId Nothing $ notAppl i) (Just (InitArray Nothing arr'))
        tcLocalVars pV tyV fin vds (vd:acc) cont

    Nothing -> fail $ "Variable " ++ prettyPrint i
                        ++ " of non-array type " ++ prettyPrint tyV
                        ++ " given literal array initializer"

tcLocalVars _ _ _ (vd:_) _ _ =
    fail $ "Deprecated array syntax not supported: " ++ prettyPrint vd


localVarPol :: [Modifier SourcePos] -> [VarDecl SourcePos] -> TcCodeM PL.ActorPolicy
localVarPol ms vds =
    case [ p | Reads _ p <- ms ] of
      [] -> newMetaPolVar . getVarId . head $ vds     -- TODO a TcVarPolicy for each variable, or a shared one ?
            where getVarId (VarDecl _ (VarId _ i) _) = i
                  getVarId (VarDecl _ (VarDeclArray sp vdi) _) = getVarId $ VarDecl sp vdi Nothing
      [p] -> do
        debugPrint $ "Found read policy: " ++ prettyPrint p ++ " - evaluating"
        PL.VarPolicy <$> evalPolicy p
--        liftTcDeclM $ PL.VarPolicy <$> evalPolicy p
      _ -> fail "Only one read policy allowed on local variable"

---------------------------------------------------
-- Typechecking Explicit Constructor Invocations --
---------------------------------------------------

tcEci :: TypeCheck TcCodeM ExplConstrInv
tcEci eci = do
  (tyT, nwtas, as, con) <-
      case eci of
        ThisInvoke  _ nwtas as -> (,nwtas,as,ThisInvoke)  <$> getThisType
        SuperInvoke _ nwtas as -> (,nwtas,as,SuperInvoke) <$> getSuperType
        _ -> fail $ "PrimarySuperInvoke not yet supported: " ++ prettyPrint eci
  (_,_,tasT,asT,_) <- tcCreate tyT (map (\a -> ActualArg (ann a) a) nwtas) as
  let nwtasT = map (\(ActualArg _ nwta) -> nwta) tasT
  return $ con Nothing nwtasT asT

-- | Checks whether a non-void method has at least one return statement.
--   Doesn't care about the types (they have been checked before).
checkReturnStmts :: MethodBody SourcePos -> TcCodeM ()
checkReturnStmts (MethodBody sp mBlock) = do
  (retType, _) <- getReturn
  unless (retType == voidT) $ do
    case mBlock of
      Nothing -> failEC () $ mkError MissingReturnStatement sp
      Just (Block _ blStmts) -> do
        let foundReturn = checkReturnStmts' blStmts False
        check foundReturn $ mkError MissingReturnStatement sp

  where checkReturnStmts' :: [BlockStmt a] -> Bool -> Bool
        checkReturnStmts' [] foundReturn = foundReturn
        checkReturnStmts' (blStmt:blStmts) foundReturn =
          case blStmt of
            BlockStmt _ stmt -> checkStmt stmt
            _ -> checkReturnStmts' blStmts foundReturn

          where checkStmt stmt =
                  case stmt of
                    StmtBlock _ block ->
                      checkBlockStmt block || checkReturnStmts' blStmts foundReturn

                    IfThen {} ->
                      checkReturnStmts' blStmts foundReturn

                    IfThenElse _ _ thenStmt elseStmt ->
                      checkStmt thenStmt && checkStmt elseStmt || checkReturnStmts' blStmts foundReturn

                    While _ expr bodyStmt ->
                      case expr of
                        -- TODO: handle unreachable code as Java (break from infinite loop)
                        Lit _ (Boolean _ True) -> checkStmt bodyStmt || checkReturnStmts' blStmts foundReturn
                        _ -> checkReturnStmts' blStmts foundReturn

                    Switch _ _ swBlocks ->
                      -- NOTE: relying on handling of duplication of default label
                      or [ checkReturnStmts' bls foundReturn | (SwitchBlock _ Default{} bls) <- swBlocks ] ||
                      checkReturnStmts' blStmts foundReturn

                    Do _ bodyStmt _ ->
                      -- TODO: handle unreachable code as Java (break from infinite loop)
                      checkStmt bodyStmt || checkReturnStmts' blStmts foundReturn

                    Return {} ->
                      checkReturnStmts' blStmts True

                    Try _ block catches mFinBlock ->
                      -- TODO: handle unreachable code as Java (after return in finally)
                      (checkBlockStmt block &&
                       all (\(Catch _ _ bl) -> checkBlockStmt bl) catches) ||
                       maybe False checkBlockStmt mFinBlock ||
                       checkReturnStmts' blStmts foundReturn

                    Labeled _ _ stmt' ->
                      checkStmt stmt' || checkReturnStmts' blStmts foundReturn

                    OpenBlock _ _ block ->
                      checkBlockStmt block || checkReturnStmts' blStmts foundReturn

                    _ -> checkReturnStmts' blStmts foundReturn

                  where checkBlockStmt (Block _ blStmts') = checkReturnStmts' blStmts' foundReturn

---------------------------
--   Helper functions    --
---------------------------

isFinal :: [Modifier SourcePos] -> Bool
isFinal = (Final defaultPos `elem`)
