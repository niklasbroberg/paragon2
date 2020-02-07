{-# LANGUAGE DeriveFunctor, ScopedTypeVariables, Rank2Types #-}
module Language.Java.Paragon.TypeCheck.Interpreter where

import Language.Java.Paragon.Interaction
import Language.Java.Paragon.Error
import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.SourcePos

import qualified Language.Java.Paragon.PolicyLang as PL

import {-# SOURCE #-} Language.Java.Paragon.TypeCheck.Monad.TcDeclM
import Language.Java.Paragon.TypeCheck.TypeMap
import Language.Java.Paragon.TypeCheck.Types

import qualified Data.Map as Map
import Control.Monad (forM_, ap, (>=>), void)

import Data.Maybe (fromJust)
import Data.List (nub, delete)

import qualified Control.Monad.Fail as Fail

interpretModule :: String
interpretModule = typeCheckerBase ++ ".Interpreter"

data Value = VLit (Literal SourcePos)
           | VPol PL.PrgPolicy
           | VAct PL.TypedActorIdSpec
           | VArr [Value]
  deriving (Show,Eq)

----------------------------------------
-- Monad for evaluating typemethods

data InterpretM a
    = ReturnM a
    | MethodReturn Value
    | GetVariable (Name  SourcePos) (Value -> InterpretM a)
    | SetVariable (Ident SourcePos) Value (InterpretM a)
    | CallMethod (Name SourcePos) [Value] (Value -> InterpretM a)
    | EvalType (RefType SourcePos) (TcRefType -> InterpretM a)
    | SubTypeOf TcRefType TcRefType (Bool -> InterpretM a)
  deriving Functor

instance Show (InterpretM a) where
  show (ReturnM _x) = "ReturnM (...)"
  show (MethodReturn v) = "MethodReturn (" ++ show v ++ ")"
  show (GetVariable n _f) = "GetVariable (" ++ show n ++ ") ..."
  show (SetVariable i v _k) = "SetVariable (" ++ show i ++ ") (" ++ show v ++ ") ..."
  show (CallMethod n vs _f) = "CallMethod (" ++ show n ++ ") (" ++ show vs ++ ") ..."
  show (EvalType rt _f) = "EvalType (" ++ show rt ++ ") ..."
  show (SubTypeOf rt1 rt2 _f) = "SubTypeOf (" ++ show rt1 ++ ") (" ++ show rt2 ++ ") ..."
  -- Break, Continued
  -- Loop?

instance Fail.MonadFail InterpretM where
  fail = error

instance Monad InterpretM where
  return = ReturnM
  ReturnM a >>= k = k a
  MethodReturn v >>= _ = MethodReturn v
  GetVariable n f >>= k =
      GetVariable n(f >=> k)
  SetVariable i v m >>= k =
      SetVariable i v (m >>= k)
  CallMethod n as f >>= k =
      CallMethod n as (f >=> k)
  EvalType rt f >>= k = EvalType rt (f >=> k)
  SubTypeOf rt1 rt2 f >>= k = SubTypeOf rt1 rt2 (f >=> k)

instance Applicative InterpretM where
  pure = return
  (<*>) = ap

instance HasSubTyping InterpretM where
  subTypeOf rt1 rt2 = SubTypeOf rt1 rt2 ReturnM

-- instance Functor InterpretM where

-- Dummy implementation, for now
--lookupVarC :: Name SourcePos -> TcCodeM Value
--lookupVarC n = liftTcDeclM $ lookupFieldD n
type VMap = Map (Ident SourcePos) Value

interpretPolicy :: forall m . (EvalPolicyM m) =>
                   (Name SourcePos -> m Value) -> Exp SourcePos -> m PL.PrgPolicy
interpretPolicy lokup e = do
  VPol p <- runInterpretM lokup $ iExp e
  return p

interpretTypeMethod :: forall m . (EvalPolicyM m) =>
                       (Name SourcePos -> m Value) -> MethodInvocation SourcePos -> m PL.PrgPolicy
interpretTypeMethod lokup mi = do
  VPol p <- runInterpretM lokup $ iMethodInv mi
  return p

interpretActorId :: forall m . (EvalPolicyM m) =>
                   (Name SourcePos -> m Value) -> Name SourcePos -> m PL.TypedActorIdSpec
interpretActorId lokup n@(Name spos _ _ _) =
  runInterpretM lokup $ iActorName (ActorName spos n)

interpretActor :: forall m . (EvalPolicyM m) =>
                  (Name SourcePos -> m Value) -> [(Ident SourcePos, TcRefType)] -> Actor SourcePos -> m PL.ActorSetRep
interpretActor lokup tys act =
  runInterpretM lokup $ iActor tys act -- TODO: Where is this ever used?

--interpretAtom lokup atom = do
--  runInterpretM lokup $ iAtom atom


runInterpretM :: forall m . (EvalPolicyM m) =>
                 (Name SourcePos -> m Value) -> (forall a . InterpretM a -> m a)
runInterpretM lokup = runReturnIM Map.empty
  where
    runIM :: (VMap -> InterpretM a -> m b) -> VMap -> InterpretM a -> m b
--    runIM _ (MethodReturn v) = return v
    runIM rec vs (GetVariable (Name _ _ Nothing i) f) |
      Just v <- Map.lookup i vs = rec vs (f v)
    runIM rec vs (GetVariable n f) = do
      debugPrint $ "runInterpretM[GetVariable]: " ++ prettyPrint n
      v <- lokup n
      rec vs (f v)

    runIM rec vs (SetVariable i v m) =
        rec (Map.insert i v vs) m

    runIM rec vs em@(CallMethod n as f) = do
        tm <- liftTcDeclM getTypeMap
        case lookupNamed typemethods n tm of
          Nothing -> case n of
                       Name _ _ (Just tname@(Name _ TName _ _)) i -> do
                           liftTcDeclM $ fetchType tname
                           runIM rec vs em
                       _ -> panic (interpretModule ++ ".runInterpretM") $
                            "Unknown typemethod: " ++ prettyPrint n
          Just (ps, bl) -> do
            let vs' = Map.fromList $ zip (map (Ident defaultPos) ps) as
            v <- runMethodIM vs' $ iBlock bl
            rec vs (f v)

    runIM rec vs (EvalType rt f) = do
      debugPrint $ "runInterpretM[EvalType]: " ++ show rt
      rTy <- evalSrcRefType PL.bottomM rt
      rec vs (f rTy)

    runIM rec vs (SubTypeOf rt1 rt2 f) = do
      b <- subTypeOf rt1 rt2
      rec vs (f b)

    runIM _ _ im = failE $ toUndef $ "No value returned from typemethod: " ++ show im

    runMethodIM :: VMap -> InterpretM () -> m Value
    runMethodIM _ (MethodReturn v) = return v
    runMethodIM vm im = runIM runMethodIM vm im

    runReturnIM :: VMap -> InterpretM a -> m a
    runReturnIM _ (ReturnM v) = return v
    runReturnIM vm im = runIM runReturnIM vm im

getVar :: Name SourcePos -> InterpretM Value
getVar n = GetVariable n ReturnM

setVar :: Ident SourcePos -> Value -> InterpretM SourcePos
setVar i@(Ident spos _) v = SetVariable i v (ReturnM spos)

getReturnedValue :: InterpretM a -> InterpretM Value
getReturnedValue (MethodReturn v) = return v
getReturnedValue im = panic (interpretModule ++ ".getReturnedValue")
                      $ "No return from method call: " ++ show im


---------------------
-- The interpreter --
---------------------

iBlock :: Block SourcePos -> InterpretM ()
iBlock (Block _ bstmts) = mapM_ iBlockStmt bstmts

iBlockStmt :: BlockStmt SourcePos -> InterpretM ()
iBlockStmt (BlockStmt _ stmt) = iStmt stmt
iBlockStmt (LocalVars _ _ ty vds) = mapM_ (iVarDecl ty) vds

iVarDecl :: Type SourcePos -> VarDecl SourcePos -> InterpretM SourcePos
iVarDecl (PrimType _ pt) (VarDecl _ (VarId _ i) mInit) = do
  val <- case mInit of
           Nothing -> defaultVal pt
           Just init_ -> iVarInit init_
  setVar i val

    where defaultVal :: PrimType SourcePos -> InterpretM Value
          defaultVal (BooleanT spos) = return $ VLit $ Boolean spos False
          defaultVal (IntT     spos) = return $ VLit $ Int spos 0
          defaultVal _ = fail "defaultVal: Unsupported uninitialized variable"

iVarInit :: VarInit SourcePos -> InterpretM Value
iVarInit (InitExp _ init_) = iExp init_
iVarInit (InitArray _ (ArrayInit _ vinits)) = VArr <$> mapM iVarInit vinits

iStmt :: Stmt SourcePos -> InterpretM ()
iStmt s =
    case s of
      IfThen _ c stmt -> do
             b <- iBool c
             if b then iStmt stmt else return ()
      IfThenElse _ c th el -> do
             b <- iBool c
             if b then iStmt th else iStmt el
      While _ c stmt -> do
             b <- iBool c
             if b then iStmt stmt >> iStmt s else return ()
      EnhancedFor _ _ _ i e stmt -> do
             VArr vs <- iExp e
             forM_ vs $ \v -> do
               setVar i v
               iStmt stmt
      ExpStmt _ e -> void (iExp e)
      Return _ (Just e) -> do
             v <- iExp e
             MethodReturn v
      _ -> panic (interpretModule ++ ".iStmt")
           "Unsupported statement in typemethod"

iBool :: Exp SourcePos -> InterpretM Bool
iBool e = do
  VLit (Boolean _ b) <- iExp e
  return b


iExp :: Exp SourcePos -> InterpretM Value
iExp e =
    case e of
      Lit _ l -> return $ VLit l
      Paren _ e1 -> iExp e1
      ExpName _ n -> getVar n
      MethodInv _ mi -> iMethodInv mi
      BinOp _ e1 op e2 -> iOp op e1 e2
      PolicyExp _ pe -> iPolicyExp pe
      _ -> panic (interpretModule ++ ".iExp") $
           "Unhandled case: " ++ show e

iPolicyExp :: PolicyExp SourcePos -> InterpretM Value
iPolicyExp pe = VPol <$>
    case pe of
      PolicyLit _ cs -> PL.ConcretePolicy <$> (PL.Policy <$> mapM iClause cs)
      PolicyOf  _ i  -> return $ PL.PolicyVar $ PL.PolicyOfVar (unIdent i)
      PolicyThis _   -> return $ PL.PolicyVar PL.ThisVar
      PolicyTypeVar _ i -> return $ PL.PolicyVar $ PL.PolicyTypeParam (unIdent i)

iClause :: Clause SourcePos -> InterpretM PL.TcClause
iClause (Clause _ cvds chead atoms) = do
  iTysCvds <- mapM iClauseVarDecl cvds
  (hActor, hActset, iTys) <- iClauseHead iTysCvds chead
  let allQs = nub $ delete hActor $ concatMap extractActors atoms
      actMap = (hActor, PL.HeadActor) : zip allQs (map PL.QuantActor [0..])
  qs <- mapM (iActor iTys) allQs
  return $ PL.Clause hActset qs $ map (generalizeAtom actMap) atoms
         where extractActors :: Atom SourcePos -> [Actor SourcePos]
               extractActors (Atom _ _ as) = as

               --cheadToActor :: ClauseHead SourcePos -> Actor SourcePos
               --cheadToActor (ClauseDeclHead _ (ClauseVarDecl _ rt i)) =
               --    undefined

iClauseVarDecl :: ClauseVarDecl SourcePos -> InterpretM (Ident SourcePos, TcRefType)
iClauseVarDecl (ClauseVarDecl _ rt i) = do
  rTy <- iRefType rt
  return (i, rTy)

iClauseHead :: [(Ident SourcePos, TcRefType)]
            -> ClauseHead SourcePos
            -> InterpretM (Actor SourcePos, PL.TcActor, [(Ident SourcePos, TcRefType)])
iClauseHead iTys (ClauseDeclHead n (ClauseVarDecl _ rt i)) = do
  rTy <- iRefType rt
  return (Var n i, PL.TypedActor rTy (unIdent i), (i,rTy):iTys)
iClauseHead iTys (ClauseVarHead _ act) = do
  hAct <- iActor iTys act
  return (act, hAct, iTys)

iRefType :: RefType SourcePos -> InterpretM TcRefType
iRefType rt = EvalType rt ReturnM

--iClauseHead :: ClauseHead SourcePos -> InterpretM PL.TcActor
--iClauseHead (ClauseDeclHead _ cvd) = iClauseVarDecl cvd
--iClauseHead (ClauseVarHead  _ act) = iActor act

--iClauseVarDecl :: ClauseVarDecl SourcePos -> InterpretM PL.TcActor
--iClauseVarDecl (ClauseVarDecl _ rt i) = return $ PL.TypedActor rt $ unIdent i

generalizeAtom :: [(Actor SourcePos, PL.ActorRep)] -> Atom SourcePos -> PL.TcAtom
generalizeAtom actMap (Atom _ n as) = PL.Atom n $ map convertActor as
  where convertActor a = fromJust $ lookup a actMap


--iAtom :: Atom SourcePos -> InterpretM PL.TcAtom
--iAtom (Atom _ n as) = PL.Atom n <$> mapM (iActorRep actMap) as

--iLClause :: LClause SourcePos -> InterpretM (TcClause TcAtom)
--iLClause (LClause _ hatom atoms) = TcClause <$> iAtom hatom <*> mapM iAtom atoms

--iActorRep :: [(Actor SourcePos, PL.ActorRep)] -> Actor SourcePos -> InterpretM PL.ActorRep
--iActorRep actMap (Actor _ aname)


iActor :: [(Ident SourcePos, TcRefType)] -> Actor SourcePos -> InterpretM PL.TcActor
iActor iTys (Actor _ aname) = PL.SingletonActor <$> iActorName aname
iActor iTys (Var _ i) = do
    let Just rTy = lookup i iTys -- We will know the types for all Vars
    return $ PL.TypedActor rTy $ unIdent i

iActorName :: ActorName SourcePos -> InterpretM PL.TypedActorIdSpec
iActorName (ActorName _ n) = do
  VAct aid <- getVar n
  return aid
iActorName (ActorTypeVar _ rt i) = do
  rTy <- iRefType rt
  return $ PL.TypedActorIdSpec rTy $ PL.ActorTPVar $ unIdent i


iOp :: Op SourcePos -> Exp SourcePos -> Exp SourcePos -> InterpretM Value
iOp op e1 e2 =
    case op of
      -- "conditional and/or" need different treatment
      CAnd sp -> do
              b <- iBool e1
              if b then iExp e2
                   else return $ VLit (Boolean sp False)
      COr  sp -> do
              b <- iBool e1
              if b then return $ VLit (Boolean sp True)
                   else iExp e2

      -- the rest are all strict
      _ -> do
        v1 <- iExp e1
        v2 <- iExp e2
        case op of
          Mult _ -> case (v1, v2) of
                      (VPol pca, VPol pcb) -> VPol <$> pca `PL.lub` pcb
                      (VLit (Int spA i1), VLit (Int spB i2)) -> return $ VLit $ Int spA $ i1*i2
          Add  _ -> case (v1, v2) of
                      (VPol pca, VPol pcb) -> VPol <$> pca `PL.glb` pcb
          _ -> fail $ "iOp: operator not yet implemented: " ++ prettyPrint op

iMethodInv :: MethodInvocation SourcePos -> InterpretM Value
iMethodInv (MethodCallOrLockQuery _ n as) =
    do vs <- mapM iExp as
       CallMethod n vs ReturnM

{---
-- This module is for interpreting compile-time functions,
-- for evaluating policy expressions. The only possible
-- return type will be 'policy', which during type-checking
-- means a PolicyCT.

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty

--import qualified Language.Java.Paragon.TypeChecker.PriorityMap as PM
import qualified Data.Map as Map

import Language.Java.Paragon.TypeCheck.Policy
import Language.Java.Paragon.TypeCheck.Actors
import Language.Java.Paragon.TypeCheck.TcEnv

import Control.Monad (when)
import Control.Applicative ((<$>))
import Control.Arrow (first, second)

data Value = VLit Literal
           | VPol PolicyCT
           | VAct ActorId
           | VArr [Value]
  deriving (Show,Eq)

type IState = (PM.PriorityMap Name Value, TypeEnv)


runIM :: TypeEnv -> IM a -> PolicyCT
runIM te (IM f) = case f (PM.empty, te) of
                    Left pct -> pct
                    Right _ -> error "runIM"

newtype IM a = IM (IState -> Either PolicyCT (a, IState))

instance Functor IM where
  fmap f (IM g) = IM $ \istate -> case g istate of
                                   Left pct -> Left pct
                                   Right (a, newState) -> Right (f a, newState)

instance Monad IM where
  return x = IM $ \ist -> Right (x, ist)

  (IM f) >>= k = IM $ \ist ->
      case f ist of
        Right (a, newst) -> let (IM g) = k a in g newst
        Left pct -> Left pct

getState :: IM IState
getState = IM $ \ist -> Right (ist, ist)

setState :: IState -> IM SourcePos
setState ist = IM $ \_ -> Right ((), ist)

updateState :: (IState -> IState) -> IM SourcePos
updateState f = do
  st <- getState
  setState $ f st

scoped :: IM a -> IM a
scoped ima = do
  updateState (first PM.extend)
  a <- ima
  updateState (first PM.shrink)
  return a


getVar :: Name -> IM Value
getVar n = do
  (state, _) <- getState
  case PM.lookup n state of
    Just val -> return val
    Nothing  -> error $ "Internal server error: getVar: " ++ prettyPrint n

setVar :: Name -> Value -> IM SourcePos
setVar n v = updateState (first $ PM.insert n v)

final :: PolicyCT -> IM SourcePos
final pct = IM (\_ -> Left pct)




---------------------------------

iStmt :: Stmt -> IM SourcePos
iStmt s = case s of
    Return (Just e) -> do
        pct <- evalPCT e
        final pct

    StmtBlock bl -> iBlock bl
    IfThen e th  -> do
        b <- evalBool e
        when b $ iStmt th
    IfThenElse e th el -> do
        b <- evalBool e
        iStmt $ if b then th else el
    While e st -> do
        b <- evalBool e
        when b $ do
               iStmt st
               iStmt $ While e st
    BasicFor (mInit) (mCheck) (mUps) st ->
        undefined
    EnhancedFor _ _ i arr st -> do
        arrv <- evalArr arr
        mapM_ (\v -> do setVar (Name [i]) v
                        iStmt st) arrv
    Empty -> return ()
    ExpStmt e -> iExp e >>= \_ -> return ()
    Do st e -> do
        iStmt st
        b <- evalBool e
        when b $ iStmt $ Do st e
    _ -> error $ "Stmt not supported in compile-time code: " ++ prettyPrint s


iBlock :: Block -> IM ()
iBlock (Block bss) = scoped $ mapM_ iBlockStmt bss

iBlockStmt :: BlockStmt -> IM ()
iBlockStmt bs = case bs of
                  BlockStmt stmt -> iStmt stmt
                  LocalVars _ _ vds -> mapM_ iVarDecl vds
                  _ -> error $ "BlockStmt not supported in compile-time code: " ++ prettyPrint bs


iVarDecl :: VarDecl -> IM ()
iVarDecl (VarDecl (VarId i) mInit) = do
  case mInit of
    Nothing -> setVar (Name [i]) (error $ "Variable not initialized: " ++ prettyPrint i)
    Just init -> do
       v <- iVarInit init
       setVar (Name [i]) v

iVarInit :: VarInit -> IM Value
iVarInit (InitExp init) = iExp init
iVarInit (InitArray (ArrayInit vinits)) = VArr <$> mapM iVarInit vinits



evalArr :: Exp -> IM [Value]
evalArr e = do
  val <- iExp e
  case val of
    VArr vals -> return vals
    _ -> error $ "Internal compiler error: evalArr: " ++ prettyPrint e

{-
evalArrField :: Exp -> IM ([Value], Name, [Int])
evalArrField e = do
  (val, n, is) <- iField e
  case val of
    VArr vals -> return (vals, n, is)
    _ -> error $ "Internal compiler error: evalArrField: " ++ prettyPrint e
-}



evalBool :: Exp -> IM Bool
evalBool e = do
  val <- iExp e
  case val of
    VLit (Boolean b) -> return b
    _ -> error $ "Internal compiler error: evalBool: " ++ prettyPrint e

evalPCT :: Exp -> IM PolicyCT
evalPCT e = do
  val <- iExp e
  case val of
    VPol pct -> return pct
    _ -> error $ "Internal compiler error: evalPCT: " ++ prettyPrint e

evalInt :: Exp -> IM Int
evalInt e = do
  val <- iExp e
  case val of
    VLit (Int k) -> return $ fromIntegral k
    _ -> error $ "Internal compiler error: evalInt: " ++ prettyPrint e


iField :: Exp -> IM (Name, [Int])
iField e = case e of
    ExpName n -> do
      return (n, [])
{-    ArrayAccess (ArrayIndex e1 e2) -> do
      (n, is) <- iField e1
      index <- evalInt e2
      return (arr!!index, n, index:is)-}
--    PostIncrement e -> do
--                    (v, n, is) <- iField e


iExp :: Exp -> IM Value
iExp e = case e of
    Lit l -> return $ VLit l
    Paren e -> iExp e
    ExpName n -> getVar n
    BinOp e1 op e2 -> evalOp op e1 e2
    ArrayAccess (ArrayIndex e1 e2) -> do
                  arr <- evalArr e1
                  index <- evalInt e2
                  return $ arr!!index
{-    PostIncrement e -> do
                  (n, is) <- iField e
                  v <- getVar n
                  setVar n (inc is v)
                  return $ get is v
    PostDecrement e -> do
                  (n, is) <- iField e
                  v <- getVar n
                  setVar n (dec is v)
                  return $ get is v
    PreIncrement e -> do
                  (n, is) <- iField e
                  v <- getVar n
                  let newV = inc is v
                  setVar n newV
                  return $ newV
    PreDecrement (ExpName n) -> do
                  v <- getVar n
                  let newV = dec v
                  setVar n newV
                  return newV -}
    Assign lhs aOp e -> iAssign lhs aOp e
    MethodInv mi -> iMethodInv mi
    PolicyExp pl -> VPol <$> iPolicyLit pl

iPolicyLit :: PolicyLit -> IM PolicyCT
iPolicyLit (PolicyLit cs) = PolicyCT <$> mapM iClause cs
  where iClause :: Clause Actor -> IM (ClauseCT ActorCT)
        iClause (Clause h b) = do
          ha  <- iActor h
          bas <- mapM iAtom b
          return $ ClauseCT ha bas
        iAtom :: Atom -> IM AtomCT
        iAtom (Atom ln as) = do
          aIds <- mapM iActor as
          return $ AtomCT ln aIds
        iActor :: Actor -> IM ActorCT
        iActor (Actor n) = getVar n >>= \(VAct aid) -> return $ ActorCT aid
        iActor (Var i)   = return $ VarCT i


iMethodInv :: MethodInvocation -> IM Value
iMethodInv mi = undefined

iAssign :: Lhs -> AssignOp -> Exp -> IM Value
iAssign lhs aOp e = do
  (n, is) <- iLhs lhs
  v <- iExp e
  assignOp aOp n is v

assignOp :: AssignOp -> Name -> [Int] -> Value -> IM Value
assignOp aOp n [] v =
      do oldV <- getVar n
         let newV = case aOp of
                      EqualA -> v
                      MultA  -> case (oldV, v) of
                                  (VPol pca, VPol pcb) -> VPol $ pca `join` pcb
                                  (VLit (Int i1), VLit (Int i2)) -> VLit $ Int $ i1*i2
                      AddA   -> case (oldV, v) of
                                  (VPol pca, VPol pcb) -> VPol $ pca `meet` pcb
                                  (VLit (Int i1), VLit (Int i2)) -> VLit $ Int $ i1+i2
                      _ -> error $ "Internal compiler error: assignOp: " ++ prettyPrint aOp
         setVar n newV
         return newV


iLhs :: Lhs -> IM (Name, [Int])
iLhs (NameLhs n) = return (n, [])
iLhs lhs = error $ "Internal compiler error: non-name lhs not yet supported: " ++ prettyPrint lhs



inc, dec :: Value -> Value
inc (VLit (Int i)) = VLit (Int $ i+1)
inc _ = error $ "Internal compiler error: inc"

dec (VLit (Int i)) = VLit (Int $ i-1)
dec _ = error $ "Internal compiler error: dec"

evalOp :: Op -> Exp -> Exp -> IM Value
evalOp op e1 e2 =
    case op of
      -- "conditional and/or" need different treatment
      CAnd -> do
              b <- evalBool e1
              if b then iExp e2
                   else return $ VLit (Boolean False)
      COr  -> do
              b <- evalBool e1
              if b then return $ VLit (Boolean True)
                   else iExp e2

      -- the rest are all strict
      _ -> do
        v1 <- iExp e1
        v2 <- iExp e2
        case op of
          Mult -> case (v1, v2) of
                    (VPol pca, VPol pcb) -> return $ VPol $ pca `join` pcb
                    (VLit (Int i1), VLit (Int i2)) -> return $ VLit $ Int $ i1*i2
          Add  -> case (v1, v2) of
                    (VPol pca, VPol pcb) -> return $ VPol $ pca `meet` pcb

{-
          Rem  -> numericOp rem v1 v2
          Sub  -> numericOp (-) v1 v2
          Div  -> divOp v1 v2 -- need separate handling

          LThan -> numericOp (<) v1 v2
          GThan -> numericOp (>) v1 v2
          LThanE -> numericOp (<=) v1 v2
          GThanE -> numericOp (>=) v1 v2
          Equal  -> anyOp (==) v1 v2
          NotEq  -> anyOp (/=) v1 v2

          And -> boolOp strictAnd v1 v2
          Or  -> boolOp (||) v1 v2
          Xor -> boolOp xor v1 v2
-}

-}
