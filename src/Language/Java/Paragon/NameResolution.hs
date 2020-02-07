{-# LANGUAGE TupleSections, Rank2Types #-}
-- | This module implements the name resolution stage of the compiler
module Language.Java.Paragon.NameResolution (resolveNames) where

import Language.Java.Paragon.Error
import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.SourcePos
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.NameResolution.Monad

import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as B

import Control.Applicative
import Control.Monad (unless)
import Data.Traversable
import Data.List (nub)
import Data.Maybe (maybeToList)
import Prelude hiding (mapM)

nameResModule :: String
nameResModule = libraryBase ++ ".NameResolution"

------------------------------------------
-- Top level exported function

-- | Resolve names in a single compilation unit (.para file)
-- Returns annotated compilation unit
-- Name resolution based on .pi files in the given pipath
resolveNames :: PiPath
             -> CompilationUnit SourcePos
             -> BaseM (CompilationUnit SourcePos)
resolveNames piPath (CompilationUnit pos pkg imps [td])
 = runPiReader piPath $ do

  -- 1. Expand definitions from java.lang
  (_, javaLangExpnMap) <- buildMapFromImportName $
       TypeImportOnDemand defaultPos (mkName const PName PName $
           map (Ident defaultPos . B.pack) ["java", "lang"])

  -- 2. Expand definitions from imports
  (imps', impExpnMap) <- buildMapFromImports imps

  -- 3. Expand definitions from pi path
  piExpnMap           <- buildMapFromPiPath

  -- 4. Expand definitions from surrounding package
  pkgExpnMap          <- buildMapFromPkg pkg

  -- 5. Expand definition of and in the type itself & its super-types
  let jipExpnMap = unionExpnMaps [javaExpnMap, javaLangExpnMap,
                                  impExpnMap, piExpnMap, pkgExpnMap]
  (thisFullName,tnExpnMap,supExpnMap) <- buildMapFromTd (unPkgDecl pkg) td jipExpnMap

  -- 6. Construct final expansion context according to precedence rule
  -- (I.e. local definitions hide definitions in super types hide other defs)
  let expnMap = Map.union tnExpnMap (unionExpnMaps [jipExpnMap,supExpnMap])

  -- 7. Now we can finally annotate the AST, resolving all names in the type
  -- declaration using the painstakingly constructed expansion map
  --debugPrint $ "Expansions: "
  --mapM_ (debugPrint . show) $ Map.toList expnMap
  td' <- runNameRes (rnTypeDecl td) thisFullName expnMap
  return $ CompilationUnit pos pkg imps' [td']

resolveNames _ _ = failE . mkErrorFromInfo $ UnsupportedFeature "Encountered multiple type declarations in the same file"


-- | Extract Name from package declaration
unPkgDecl :: Maybe (PackageDecl SourcePos) -> Maybe (Name SourcePos)
unPkgDecl = fmap (\(PackageDecl _ n) -> n)

-------------------------------------------
-- Resolving names throughout the AST -- Boiler plate alert!!

-- | Resolution of an entity is a transformation of that entity that lives
-- in the NameRes monad
type Resolve ast = ast SourcePos -> NameRes (ast SourcePos)

mkTpsExpn :: [TypeParam SourcePos] -> Expansion
mkTpsExpn tps =
    expandAll $ newER {
          expandTypes = [ tI | TypeParam _ tI _ <- tps ],
          expandLocks = [ lI | LockStateParam _ lI <- tps ],
          expandExps  = [aI | ActorParam _ _rt aI <- tps ]
                          ++ [ pI | PolicyParam _ pI <- tps ] }

rnTypeDecl :: Resolve TypeDecl
rnTypeDecl (ClassTypeDecl pos (ClassDecl pos' ms ci tps mSuper impls cb)) = do
    extendExpansion (mkTpsExpn tps) $
      ClassTypeDecl pos <$>
          (ClassDecl pos'
              <$> mapM rnModifier ms
              <*> pure ci
              <*> mapM rnTypeParam tps -- relevant because of wildcards
              <*> mapM rnClassType mSuper
              <*> mapM rnClassType impls
              <*> rnClassBody cb)
rnTypeDecl (InterfaceTypeDecl pos (InterfaceDecl pos' ms ii tps supers ib)) = do
    extendExpansion (mkTpsExpn tps) $
      InterfaceTypeDecl pos <$>
          (InterfaceDecl pos'
              <$> mapM rnModifier ms
              <*> pure ii
              <*> mapM rnTypeParam tps -- relevant because of wildcards
              <*> mapM rnClassType supers
              <*> rnInterfaceBody ib)
rnTypeDecl _ = failE . mkErrorFromInfo $
                 UnsupportedFeature "Enum declarations not yet supported"

rnClassBody :: Resolve ClassBody
rnClassBody (ClassBody pos ds) = do
  let fns =     [ vI | MemberDecl _ (FieldDecl  _ _ _   vds     ) <- ds  ,
                       VarDecl    _ (VarId      _       vI) _     <- vds ]
      mns = nub [ mI | MemberDecl _ (MethodDecl _ _ _ _ mI _ _ _) <- ds  ]
      lns =     [ lI | MemberDecl _ (LockDecl   _ _     lI _ _  ) <- ds  ]

      expns = expandAll $ newER {
        expandLocks = lns,
        expandMethods = mns,
        expandExps = fns }

  extendExpansion expns $ do -- left-biased
      ClassBody pos <$> mapM rnDecl ds

rnInterfaceBody :: Resolve InterfaceBody
rnInterfaceBody (InterfaceBody pos mds) = do
  let fns =     [ vI | FieldDecl  _ _ _   vds      <- mds  ,
                       VarDecl    _ (VarId _ vI) _ <- vds ]
      mns = nub [ mI | MethodDecl _ _ _ _ mI _ _ _ <- mds  ]
      lns =     [ lI | LockDecl   _ _     lI _ _   <- mds  ]

      expns = expandAll $ newER {
        expandLocks = lns,
        expandMethods = mns,
        expandExps = fns }

  extendExpansion expns $ -- left-biased
      InterfaceBody pos <$> mapM rnMemberDecl mds

rnDecl :: Resolve Decl
rnDecl (InitDecl pos statiic bl) = InitDecl pos statiic <$> rnBlock bl
rnDecl (MemberDecl pos md) = MemberDecl pos <$> rnMemberDecl md

rnModifier :: Resolve Modifier
rnModifier md =
    case md of
      Reads  pos pol -> Reads   pos <$> rnExp pol
      Writes pos pol -> Writes  pos <$> rnExp pol
      Opens   pos ls -> Opens   pos <$> mapM rnLock ls
      Closes  pos ls -> Closes  pos <$> mapM rnLock ls
      Expects pos ls -> Expects pos <$> mapM rnLock ls
      _ -> return md


rnMemberDecl :: Resolve MemberDecl
rnMemberDecl md = do
--    debugPrint $ "Resolving member decl: " ++ prettyPrint md
--    debugPrint $ show md ++ "\n"
    case md of
      FieldDecl pos ms t vds ->
          FieldDecl pos <$> mapM rnModifier ms <*> rnType t <*> mapM rnVarDecl vds

      MethodDecl pos ms tps ret mI fps exns mbody -> do
          let ps = [ pI | FormalParam _ _ _ _ (VarId _ pI) <- fps ]
              paramsE = expandAll $ newER { expandExps = ps }
              tpsE    = mkTpsExpn tps
          extendExpansion (unionExpnMaps [paramsE,tpsE])  $
            MethodDecl pos
              <$> mapM rnModifier ms
              <*> mapM rnTypeParam tps
              <*> rnReturnType ret
              <*> pure mI
              <*> mapM rnFormalParam fps
              <*> mapM rnExceptionSpec exns
              <*> rnMethodBody mbody

      ConstructorDecl pos ms tps cI fps exns cbody -> do
          let ps = [ pI | FormalParam _ _ _ _ (VarId _ pI) <- fps ]
              paramsE = expandAll $ newER { expandExps = ps }
              tpsE    = mkTpsExpn tps
          extendExpansion (unionExpnMaps [paramsE,tpsE])  $
            ConstructorDecl pos
              <$> mapM rnModifier ms
              <*> mapM rnTypeParam tps
              <*> pure cI
              <*> mapM rnFormalParam fps
              <*> mapM rnExceptionSpec exns
              <*> rnConstructorBody cbody

      LockDecl pos ms lI arity mProps ->
          LockDecl pos
            <$> mapM rnModifier ms
            <*> pure lI
            <*> mapM rnRefType arity
            <*> mapM rnLockProperties mProps
      decl -> do failEC decl . mkErrorFromInfo $
                  UnsupportedFeature "Inner types not supported"


rnConstructorBody :: Resolve ConstructorBody
rnConstructorBody (ConstructorBody pos mECI bss) =
    ConstructorBody pos
        <$> mapM rnExplConstrInv mECI
        <*> rnBlockStmts bss

rnExplConstrInv :: Resolve ExplConstrInv
rnExplConstrInv eci =
    case eci of
      ThisInvoke pos nwtas as ->
          ThisInvoke pos
             <$> mapM rnNonWildTypeArgument nwtas
             <*> mapM rnExp as
      SuperInvoke pos nwtas as ->
          SuperInvoke pos
             <$> mapM rnNonWildTypeArgument nwtas
             <*> mapM rnExp as
      PrimarySuperInvoke pos e nwtas as ->
          PrimarySuperInvoke pos
             <$> rnExp e
             <*> mapM rnNonWildTypeArgument nwtas
             <*> mapM rnExp as

rnMethodBody :: Resolve MethodBody
rnMethodBody (MethodBody pos mBl) = MethodBody pos <$> mapM rnBlock mBl

rnFormalParam :: Resolve FormalParam
rnFormalParam (FormalParam pos ms t ell vdi) =
    FormalParam pos
        <$> mapM rnModifier ms
        <*> rnType t
        <*> pure ell
        <*> pure vdi

rnVarDecl :: Resolve VarDecl
rnVarDecl (VarDecl pos vdi mInit) = do
  VarDecl pos vdi <$> mapM rnVarInit mInit

rnVarInit :: Resolve VarInit
rnVarInit (InitExp   pos e    ) = InitExp   pos <$> rnExp e
rnVarInit (InitArray pos aInit) = InitArray pos <$> rnArrayInit aInit

rnArrayInit :: Resolve ArrayInit
rnArrayInit (ArrayInit pos vInits) = ArrayInit pos <$> mapM rnVarInit vInits

rnExceptionSpec :: Resolve ExceptionSpec
rnExceptionSpec (ExceptionSpec pos ms et) =
    ExceptionSpec pos
        <$> mapM rnModifier ms
        <*> rnRefType et

rnBlock :: Resolve Block
rnBlock (Block pos bss) = Block pos <$> rnBlockStmts bss

rnBlockStmts :: [BlockStmt SourcePos] -> NameRes [BlockStmt SourcePos]
rnBlockStmts [] = return []
rnBlockStmts (bs:bss) = do
  (bs', bss') <- rnBlockStmt bs $ rnBlockStmts bss
  return $ bs':bss'

rnBlockStmt :: BlockStmt SourcePos
               -> NameRes a
               -> NameRes (BlockStmt SourcePos, a)
rnBlockStmt bs cont =
    case bs of
      BlockStmt pos stmt ->
            (,) <$> (BlockStmt pos <$> rnStmt stmt) <*> cont

      LocalVars pos ms t vds -> do
              lvf <- LocalVars pos
                       <$> mapM rnModifier ms
                       <*> rnType t
              (vds', a) <- rnVarDecls vds cont
              return (lvf vds', a)

      _ -> failE . mkErrorFromInfo $ UnsupportedFeature
             "Local classes or locks not yet supported"

rnVarDecls :: [VarDecl SourcePos] -> NameRes a -> NameRes ([VarDecl SourcePos], a)
rnVarDecls = rnVarDeclsAcc []

rnVarDeclsAcc :: [VarDecl SourcePos]  -- ^Accumulator (reversed)
              -> [VarDecl SourcePos]  -- ^List to resolve
              -> NameRes a -- ^What to do when all vardecls have been resolved
              -> NameRes ([VarDecl SourcePos], a) -- ^Result (re-reversed)
rnVarDeclsAcc acc [] cont = (reverse acc,) <$> cont
rnVarDeclsAcc acc (vd@(VarDecl _ (VarId _ i) _) : vds) cont = do
  let expn = mkEExpansion $ unIdent i
  extendExpansion expn $ do
    vd' <- rnVarDecl vd
    rnVarDeclsAcc (vd':acc) vds cont
rnVarDeclsAcc _ (vd:_) _ = failE . mkErrorFromInfo $ UnsupportedFeature ("Deprecated array syntax not supported: " ++ prettyPrint vd)

rnStmt :: Resolve Stmt
rnStmt stmt =
    case stmt of
      StmtBlock pos bl -> StmtBlock pos <$> rnBlock bl
      IfThen pos ec th -> IfThen pos <$> rnExp ec <*> rnStmt th
      IfThenElse pos ec th el ->
          IfThenElse pos <$> rnExp ec <*> rnStmt th <*> rnStmt el
      While pos ec st -> While pos <$> rnExp ec <*> rnStmt st

      BasicFor pos mForInit mTest mUps st -> do
                (mfi, f) <- rnForInit mForInit $
                                   (\mT mU s mfi -> BasicFor pos mfi mT mU s)
                                           <$> mapM rnExp mTest
                                           <*> mapM (mapM rnExp) mUps
                                           <*> rnStmt st
                return $ f mfi

      EnhancedFor pos ms t i e st ->
          EnhancedFor pos
              <$> mapM rnModifier ms
              <*> rnType t
              <*> pure i
              <*> rnExp e
              <*> extendExpansion (mkEExpansion $ unIdent i)
                    (rnStmt st)

      ExpStmt pos e -> ExpStmt pos <$> rnExp e
      Assert pos e mE -> Assert pos <$> rnExp e <*> mapM rnExp mE
      Switch pos e sbs -> Switch pos <$> rnExp e <*> mapM rnSwitchBlock sbs
      Do pos st ec -> Do pos <$> rnStmt st <*> rnExp ec
      Return pos mE -> Return pos <$> mapM rnExp mE
      Synchronized pos e bl -> Synchronized pos <$> rnExp e <*> rnBlock bl
      Throw pos e -> Throw pos <$> rnExp e
      Try pos bl cas mFin -> Try pos <$> rnBlock bl <*> mapM rnCatch cas <*> mapM rnBlock mFin
      Labeled pos i st -> Labeled pos i <$> rnStmt st

      Open pos l -> Open pos <$> rnLock l
      Close pos l -> Close pos <$> rnLock l
      OpenBlock pos l bl -> OpenBlock pos <$> rnLock l <*> rnBlock bl
      CloseBlock pos l bl -> CloseBlock pos <$> rnLock l <*> rnBlock bl

      _ -> return stmt


rnCatch :: Resolve Catch
rnCatch (Catch pos fp bl) =
  case fp of
    FormalParam posFP _ _ _ (VarId _ pI) ->
        extendExpansion (mkEExpansion $ unIdent pI) $
            Catch posFP <$> rnFormalParam fp <*> rnBlock bl
    _ -> failEC (Catch pos fp bl) . mkErrorFromInfo $
           UnsupportedFeature ("Deprecated array syntax not supported: "
                               ++ prettyPrint fp)

rnSwitchBlock :: Resolve SwitchBlock
rnSwitchBlock (SwitchBlock pos slbl bss) =
    SwitchBlock pos
        <$> rnSwitchLabel slbl
        <*> rnBlockStmts bss

rnSwitchLabel :: Resolve SwitchLabel
rnSwitchLabel (SwitchCase pos e) = SwitchCase pos <$> rnExp e
rnSwitchLabel d = return d


rnForInit :: Maybe (ForInit SourcePos) -> NameRes a -> NameRes (Maybe (ForInit SourcePos), a)
rnForInit Nothing cont = (Nothing,) <$> cont
rnForInit (Just (ForInitExps pos es)) cont =
    (,) <$> (Just . ForInitExps pos <$> mapM rnExp es) <*> cont
rnForInit (Just (ForLocalVars pos ms t vds)) cont = do
  flvf <- ForLocalVars pos
            <$> mapM rnModifier ms
            <*> rnType t

  (vds', a) <- rnVarDecls vds cont
  return (Just $ flvf vds', a)

rnExp :: Resolve Exp
rnExp expr =
    case expr of
      ClassLit pos mt -> ClassLit pos <$> mapM rnType mt
      ThisClass pos n -> ThisClass pos <$> rnName n
      Paren pos e     -> Paren pos <$> rnExp e
      InstanceCreation pos tas ct as mcb ->
          InstanceCreation pos
              <$> mapM rnTypeArgument tas
              <*> rnClassType ct
              <*> mapM rnExp as
              <*> mapM rnClassBody mcb
      qic@(QualInstanceCreation _pos _e _tas _i _as _mcb) ->
        failEC qic . mkErrorFromInfo $
          UnsupportedFeature "Inner classes not yet supported"
      ArrayCreate pos t dimExprs dims ->
          ArrayCreate pos
              <$> rnType t
              <*> (let (es, ps) = unzip dimExprs
                   in zip <$> mapM rnExp es <*> mapM (mapM rnExp) ps)
              <*> mapM (mapM rnExp) dims
      ArrayCreateInit pos t dims aInit ->
          ArrayCreateInit pos
              <$> rnType t
              <*> mapM (mapM rnExp) dims
              <*> rnArrayInit aInit
      FieldAccess   pos fa -> FieldAccess   pos <$> rnFieldAccess fa
      MethodInv     pos mi -> MethodInv     pos <$> rnMethodInvocation mi
      ArrayAccess   pos ai -> ArrayAccess   pos <$> rnArrayIndex ai
      ExpName       pos n  -> ExpName       pos <$> rnName n
      PostIncrement pos e  -> PostIncrement pos <$> rnExp e
      PostDecrement pos e  -> PostDecrement pos <$> rnExp e
      PreIncrement  pos e  -> PreIncrement  pos <$> rnExp e
      PreDecrement  pos e  -> PreDecrement  pos <$> rnExp e
      PrePlus       pos e  -> PrePlus       pos <$> rnExp e
      PreMinus      pos e  -> PreMinus      pos <$> rnExp e
      PreBitCompl   pos e  -> PreBitCompl   pos <$> rnExp e
      PreNot        pos e  -> PreNot        pos <$> rnExp e
      Cast  pos t e       -> Cast       pos <$> rnType t <*> rnExp e
      BinOp pos e1 op e2  -> BinOp      pos <$> rnExp e1 <*> pure op <*> rnExp e2
      InstanceOf pos e rt -> InstanceOf pos <$> rnExp e  <*> rnRefType rt
      Cond pos ec eth eel -> Cond       pos <$> rnExp ec <*> rnExp eth <*> rnExp eel
      Assign pos lhs aop rhs -> Assign  pos <$> rnLhs lhs <*> pure aop <*> rnExp rhs

      PolicyExp pos pe -> PolicyExp pos <$> rnPolicyExp pe
      LockExp   pos l  -> LockExp   pos <$> rnLock l -- does this even exist?

      _ -> return expr

rnLhs :: Resolve Lhs
rnLhs lhs =
    case lhs of
      NameLhs  pos n  -> NameLhs  pos <$> rnName n
      FieldLhs pos fa -> FieldLhs pos <$> rnFieldAccess fa
      ArrayLhs pos ai -> ArrayLhs pos <$> rnArrayIndex ai

rnArrayIndex :: Resolve ArrayIndex
rnArrayIndex (ArrayIndex pos arr eI) =
    ArrayIndex pos <$> rnExp arr <*> rnExp eI

rnFieldAccess :: Resolve FieldAccess
rnFieldAccess fa =
    case fa of
      PrimaryFieldAccess pos e i -> PrimaryFieldAccess pos <$> rnExp        e <*> pure i
      ClassFieldAccess   pos n i -> ClassFieldAccess   pos <$> rnName n <*> pure i
      sfa -> return sfa

rnMethodInvocation :: Resolve MethodInvocation
rnMethodInvocation mi =
    case mi of
      MethodCallOrLockQuery pos n as -> do
--          debugPrint $ "rnMethodInvocation: " ++ show n
          MethodCallOrLockQuery pos <$> rnName n <*> mapM rnExp as
      PrimaryMethodCall pos e nwtas i as ->
          PrimaryMethodCall pos
            <$> rnExp e
            <*> mapM rnNonWildTypeArgument nwtas
            <*> pure i
            <*> mapM rnExp as
      SuperMethodCall pos nwtas i as ->
          SuperMethodCall pos
            <$> mapM rnNonWildTypeArgument nwtas
            <*> pure i
            <*> mapM rnExp as
      ClassMethodCall pos n nwtas i as ->
          ClassMethodCall pos
            <$> rnName n
            <*> mapM rnNonWildTypeArgument nwtas
            <*> pure i
            <*> mapM rnExp as
      TypeMethodCall pos n nwtas i as ->
          TypeMethodCall pos
            <$> rnName n
            <*> mapM rnNonWildTypeArgument nwtas
            <*> pure i
            <*> mapM rnExp as

rnLock :: Resolve Lock
rnLock (Lock pos n as) = Lock pos <$> rnName n <*> mapM rnActorName as
rnLock lv = return lv

rnLockProperties :: Resolve LockProperties
rnLockProperties (LockProperties pos lcs) = LockProperties pos <$> mapM rnLClause lcs

rnLClause :: Resolve LClause
rnLClause (LClause pos qs a as) = do
    let ps = [ pI | ClauseVarDecl _ _ pI <- qs ]
        qualsE = expandAll $ newER { expandExps = ps }
    extendExpansion qualsE $
      LClause pos <$> mapM rnClauseVarDecl qs <*> rnAtom a <*> mapM rnAtom as
rnLClause (ConstraintClause pos qs as) = do
    let ps = [ pI | ClauseVarDecl _ _ pI <- qs ]
        qualsE = expandAll $ newER { expandExps = ps }
    extendExpansion qualsE $
      ConstraintClause pos <$> mapM rnClauseVarDecl qs <*> mapM rnAtom as

rnClause :: Resolve Clause
rnClause (Clause pos qs a as) = do
    let ps = [ pI | ClauseVarDecl _ _ pI <- qs ]
        ap = case a of
               ClauseDeclHead _ (ClauseVarDecl _ _ pI) -> (pI:)
               _ -> id
        qualsE = expandAll $ newER { expandExps = ap ps }
    extendExpansion qualsE $
      Clause pos <$> mapM rnClauseVarDecl qs <*> rnClauseHead a <*> mapM rnAtom as

rnClauseVarDecl :: Resolve ClauseVarDecl
rnClauseVarDecl (ClauseVarDecl pos rt i) =
    flip (ClauseVarDecl pos) i <$> rnRefType rt

rnClauseHead :: Resolve ClauseHead
rnClauseHead (ClauseDeclHead pos cvd) =
    ClauseDeclHead pos <$> rnClauseVarDecl cvd
rnClauseHead (ClauseVarHead pos a) = ClauseVarHead pos <$> rnActor a

rnActor :: Resolve Actor
rnActor (Actor pos an) = Actor pos <$> rnActorName an
rnActor av = return av

rnActorName :: Resolve ActorName
rnActorName (ActorName pos n) = ActorName pos <$> rnName n
rnActorName (ActorTypeVar pos rt i) = flip (ActorTypeVar pos) i <$> rnRefType rt
--rnActorName atv = return atv

rnAtom :: Resolve Atom
rnAtom (Atom pos n as) = do
  debugPrint $ "Renaming atom: " ++ prettyPrint n
  Atom pos <$> rnName n <*> mapM rnActor as

rnPolicyExp :: Resolve PolicyExp
rnPolicyExp pe =
    case pe of
      PolicyLit pos cs -> PolicyLit pos <$> mapM rnClause cs
      PolicyOf pos i -> do
              -- just see if it exists
              _ <- rnName (Name pos EName Nothing i)
              return pe
      PolicyTypeVar pos i -> do
              _ <- rnName (Name pos EName Nothing i)
              return pe
      _ -> return pe

-- Types

rnReturnType :: Resolve ReturnType
rnReturnType (Type pos t) = Type pos <$> rnType t
rnReturnType rt = return rt

rnType :: Resolve Type
rnType (RefType pos rt) = RefType pos <$> rnRefType rt
rnType t = return t

rnRefType :: Resolve RefType
rnRefType rt =
    case rt of
      ClassRefType pos ct -> ClassRefType pos <$> rnClassType ct
      ArrayType pos t dims -> do
              t' <- rnType t
              ArrayType pos t' <$> mapM (mapM rnExp) dims
      _ -> return rt

rnClassType :: Resolve ClassType
rnClassType (ClassType pos n tas) = do
  n' <- rnName n
  ClassType pos n' <$> mapM rnTypeArgument tas

rnTypeParam :: Resolve TypeParam
rnTypeParam (TypeParam pos i rts) = TypeParam pos i <$> mapM rnRefType rts
rnTypeParam (ActorParam pos rt i) = flip (ActorParam pos) i <$> rnRefType rt
rnTypeParam tp = return tp

rnTypeArgument :: Resolve TypeArgument
rnTypeArgument (ActualArg pos nwta) = ActualArg pos <$> rnNonWildTypeArgument nwta
rnTypeArgument x = failEC x . mkErrorFromInfo $
                     UnsupportedFeature "Wildcards not yet supported"

rnNonWildTypeArgument :: Resolve NonWildTypeArgument
rnNonWildTypeArgument nwta =
    case nwta of
      ActualName pos n -> ActualName pos <$> rnName n -- type, exp or lock - careful!
      ActualType pos rt -> ActualType pos <$> rnRefType rt
      ActualExp  pos e  -> ActualExp pos <$> rnExp e
      ActualLockState pos ls -> ActualLockState pos <$> mapM rnLock ls



-- Where the wild things are...

-- | The function that actually resolves a name
rnName :: Resolve Name
-- Case 1: The name has no prefix
-- => We should resolve it through expansion
-- If no expansion exists, then we should try (if applicable) to
-- resolve it as a package.
rnName n@(Name pos nt Nothing i) = do
  expn <- getExpansion
  case Map.lookup (unIdent i,nt) expn of
    Just nrAction -> do
      (mPre, resNt) <- liftEither nrAction
      return $ Name pos resNt mPre i
    Nothing -> do
{-        debugPrint $ "Unexpanded: " ++ show nam
        -- TODO: Optimize to check lazily, and store results
        let pName = Name pos PName Nothing i
            tName = Name pos TName Nothing i
        isP <- doesPkgExist  pName
        isT <- doesTypeExist tName
        case pos of
          _ | nt `elem` [AmbName, POrTName, PName] && isP -> return pName
            | nt `elem` [AmbName, POrTName, TName] && isT -> return tName
            | otherwise -> do -}
          debugPrint $ "Name: " ++ show n
          debugPrint "Expansion: "
          mapM_ (debugPrint . ("  " ++) . show) $ Map.toList expn
          failE $ Error (UnresolvedName (prettyPrint nt) (prettyPrint i)) pos []

-- Case 2: The name has a prefix
rnName (Name pos nt (Just pre) i) = do
  -- First resolve the prefix itself
  preRaw <- rnName pre

  -- If the prefix could be either expression or lock,
  -- then only the former is truly possible since locks cannot be prefixes,
  -- so we can resolve this ambiguity immediately
  let pre' = if nameType preRaw == EOrLName
              then setNameType EName preRaw
              else preRaw
      nam = Name pos nt (Just pre') i

  -- Now resolve prefixed name based on set (potentially unresolved) nametype
  case nt of
    -- Case 2a: Ambiguous name (w prefix). Look at prefix to resolve ambiguity
    AmbName -> do
      case nameType pre' of
        -- Prefix is package, so the name itself can be either a type or itself
        -- a package
        PName -> do
          withPackage pre'
               (do let tNam = setNameType TName nam
                   -- debugPrint $ "AmbName: " ++ prettyPrint tNam
                   isF <- checkForType tNam
                   if isF
                    then return tNam
                    else return $ setNameType PName nam)

        -- Prefix is type, so the name belongs to an expression (field),
        -- since we don't allow inner types.
        -- Type-checking will determine if such a field actually exists.
        TName -> return $ setNameType EName nam

        -- Prefix is member => We're accessing member of that member
        -- (Again, because no inner types allowed!)
        EName -> return $ setNameType EName nam

        -- "." not defined on any other name types,
        -- so there actually shouldn't be a prefix!
        LName    -> failEC nam $ mkError
                      (IllegalDeref "lock"           (prettyPrint nam))
                      pos
        MName    -> failEC nam $ mkError
                      (IllegalDeref "method"         (prettyPrint nam))
                      pos
        MOrLName -> failEC nam $ mkError
                      (IllegalDeref "method or lock" (prettyPrint nam))
                      pos

        _ -> panic (nameResModule ++ ".rnName")
             $ "Unexpected name: " ++ show nam

    -- Case 2b: Resolving package names (w prefix, which can only be PName)
    PName -> do
      -- See if package in scope, otherwise fail
      withPackage nam (return nam)

    -- Case 2c: Resolving package-or-type names (w prefix) by looking at the
    -- info in scope
    POrTName -> do
      let tNam = setNameType TName nam
      -- Is there a type of the name in scope?
      isT <- checkForType tNam
      if isT then return tNam
       -- If not, a package of the name?
       else do let pNam = setNameType PName nam
               isP <- doesPkgExist pNam
               if isP then return pNam
                      else failEC pNam $ mkError
                           (UnresolvedName "Package or type" (prettyPrint nam))
                           pos

    -- Case 2d: Resolving type names (w prefix)
    TName -> do
      -- See if type in scope, otherwise fail
      withTypeCurr nam (return nam)

    -- Case 2e: Resolving (candidate) expression names
    et | et `elem` [EOrLName, EName] -> do
      case nameType pre' of
        PName ->
          -- A package can only contain types directly, so this is an error
          failEC nam $ mkError
            (EInPackage (prettyPrint i) "field, variable or lock" (prettyPrint pre'))
            pos

        -- The legal cases: Prefix specifies type or expression
        -- Remaining ambiguity (in case EOrLName) must be left unresolved
        -- until typechecking!
        TName -> return nam
        EName -> return nam

        _ -> panic (nameResModule ++ ".rnName")
             $ "Unexpected name: " ++ show nam

    -- Case 2f: Resolving (candidate) method names
    mt | mt `elem` [MName, MOrLName] -> do
      case nameType pre' of
        PName ->
          -- A package can only contain types directly, so this is an error
          failEC nam $ mkError
            (EInPackage (prettyPrint i) "method or lock" (prettyPrint pre'))
            pos

        TName -> do
            -- Both methods and locks can be defined in type.
            -- We need to leave MOrLName unresolved until typechecking!
            return nam
        EName -> return nam
        _ -> panic (nameResModule ++ ".rnName")
             $ "Unexpected name: " ++ show nam

    -- Case 2g: Locks
    LName -> do
      case nameType pre' of
        PName ->
          -- A package can only contain types directly, so this is an error
          failEC nam $ mkError
            (EInPackage (prettyPrint i) "lock" (prettyPrint pre'))
            pos

        TName -> do
            -- 1st legal case: Lock accessed via type name
            -- TODO: Check here that pi file contains at least one member with name i,
            -- which must be a lock.
            return nam

        EName ->
            -- 2nd legal case: Lock accessed through member
            return nam -- defer to type checker

        _ -> panic (nameResModule ++ ".rnName")
             $ "Unexpected name: " ++ show nam

    _ -> panic (nameResModule ++ ".rnName")
         $ "Unexpected name: " ++ show nam

-- Case 3: AntiQName
rnName n = return n

-- | Union maps, but inject a suspended failure if
-- we encounter the same name several times, ambiguously
unionExpnMaps :: [Expansion] -> Expansion
unionExpnMaps expns =
    flip unionsWithKey expns
             (\(i, nt) r1 r2 -> do
                       (mPre1,_) <- r1
                       (mPre2,_) <- r2
                       unless (mPre1 == mPre2) $
                               fail $ "Ambiguous " ++ prettyPrint nt ++ " " ++ prettyPrint i ++
                                "\nCould refer to either of:" ++
                                "\n    " ++ prettyPrint (Name defaultPos AmbName mPre1 (Ident defaultPos i)) ++
                                "\n    " ++ prettyPrint (Name defaultPos AmbName mPre2 (Ident defaultPos i))
                       -- The following would work if we lifted this function
                       -- into MonadBase. Do we want to?
                       {-unless (mPre1 == mPre2) $
                               failE . mkErrorFromInfo $ AmbiguousName
                                  (prettyPrint nt)
                                  (prettyPrint i)
                                  (prettyPrint (Name pos AmbName mPre1 (Ident pos i defaultPos)))
                                  (prettyPrint (Name pos AmbName mPre2 (Ident pos i defaultPos)))-}
                       r1)


-- | Make package expansion map that contains only 'java'.
-- (The package name 'java' is always in scope.)
javaExpnMap :: Expansion
javaExpnMap =  mkPExpansion (B.pack "java")

-- | Return expansion map that contains all the types and packages
-- in the pi path
buildMapFromPiPath :: PiReader Expansion
buildMapFromPiPath = do
  (tys,pkgs) <- getPiPathContents
  return $ expansionUnion $
         map mkPExpansion pkgs ++
         map mkTExpansion tys

-- | Construct expansions for type declaration
-- The name of the surrounding package
-- Returns (fully qualified name,
--          expansion for type itself,
--          expansion for all its super types)
buildMapFromTd :: Maybe (Name SourcePos) -> TypeDecl SourcePos
               -> Expansion -> PiReader (Name SourcePos, Expansion, Expansion)
buildMapFromTd mPkgPre td expn = do
    -- Extract ident, type params, super types from type declaration
    (pos, i, tps, supers) <-
        case td of
          ClassTypeDecl     pos (ClassDecl     _ _ i tps mSuper _ _) ->
            return (pos, i, tps, maybeToList mSuper)
          InterfaceTypeDecl pos (InterfaceDecl _ _ i tps supers _  ) ->
            return (pos, i, tps, supers)
          _ -> failE . mkErrorFromInfo $
                 UnsupportedFeature "Enums not yet supported"

    -- Add package prefix to name
    let thisFullName = Name pos TName mPkgPre i

    -- Run name resolution on super types
    rnSups <- runNameRes (mapM rnClassType supers)
                         thisFullName
                         (expansionUnion [expn, mkTpsExpn tps])
    superExpns <- mapM buildMapFromSuper rnSups

    -- Type expansion for the type declaration itself
    let iExpn = mkTExpansionWithPrefix mPkgPre (unIdent i)

    return (thisFullName, iExpn, unionExpnMaps superExpns)

 where buildMapFromSuper ::  ClassType SourcePos -> PiReader Expansion
       buildMapFromSuper (ClassType _ (Name pos' _ mPre i) _) = do
         mPre' <- resolvePre mPre
         let resName = Name pos' TName mPre' i

         -- The super class/interface must of course also be a type
         withType resName
           (do -- Recurse: Build map for super types farther up the hierarchy
               CompilationUnit _ _ _ [superTd] <- getTypeContents resName
               (supSups, mDs) <- supersAndMembers superTd
               supExpns <- mapM buildMapFromSuper supSups

               -- Expand the members
               let resExpn = expandAll $ newER {
                     expandLocks =
                       [ lI | LockDecl   _ _     lI _ _   <- mDs ],
                     expandMethods =
                       nub [ mI | MethodDecl _ _ _ _ mI _ _ _ <- mDs ],
                     expandExps =
                       [ vI | FieldDecl  _ _ _   vds      <- mDs,
                                      VarDecl _ (VarId _ vI) _    <- vds ] }

               -- Combine expansions of super-super types and super type itself
               return (unionExpnMaps $ resExpn : supExpns))

       buildMapFromSuper n = panic (nameResModule ++ ".buildMapFromTd") $ show n

       -- Return list of super types and list of members of the type
       supersAndMembers :: TypeDecl SourcePos ->
                           PiReader ([ClassType SourcePos], [MemberDecl SourcePos])
       supersAndMembers superTd =
         case superTd of
           ClassTypeDecl _ (ClassDecl _ _ _ _ mSupSup _ (ClassBody _ ds))
             -> return (maybeToList mSupSup, unMemberDecls ds)
           InterfaceTypeDecl _ (InterfaceDecl _ _ _ _ supSups (InterfaceBody _ mds))
             -> return (supSups, mds)
           _ -> failE . mkErrorFromInfo $
                  UnsupportedFeature "Enums not yet supported"

       -- Extract member declarations from list of declarations
       unMemberDecls :: [Decl SourcePos] -> [MemberDecl SourcePos]
       unMemberDecls []                  = []
       unMemberDecls (MemberDecl _ d:ds) = d : unMemberDecls ds
       unMemberDecls (_:ds)              = unMemberDecls ds

-- | Build an expansion map from explicit (or implicit) imports
-- (or, incidentally, for implicit import of local package)
buildMapFromImports :: [ImportDecl SourcePos] -> PiReader ([ImportDecl SourcePos], Expansion)
buildMapFromImports imps = do
  (imps', expns) <- unzip <$> mapM buildMapFromImportName imps
  return (imps', unionExpnMaps expns)

-- | Build an expansion map from a package declaration
buildMapFromPkg :: Maybe (PackageDecl SourcePos) -> PiReader Expansion
buildMapFromPkg Nothing = return Map.empty
buildMapFromPkg (Just (PackageDecl pos n)) =
    snd <$> buildMapFromImportName (TypeImportOnDemand pos n)

-- | Build expansion map from an import declaration
-- | Returns declaration with resolved prefix and the constructed expansion
buildMapFromImportName :: ImportDecl SourcePos
                       -> PiReader (ImportDecl SourcePos, Expansion)
buildMapFromImportName imp = do
    finePrint $ "Resolving import: " ++ prettyPrint imp

    case imp of
      SingleTypeImport pos tn@(Name pos' TName mPre i) -> do
              -- Explicit import of a single type mPre.tn
              mPre' <- resolvePre mPre
              let resName = Name pos' TName mPre' i
                  resImp  = SingleTypeImport pos resName
                  resExpn = mkTExpansionWithPrefix mPre' (unIdent i)

              isTy <- doesTypeExist resName
              if isTy
               then return (resImp, resExpn)
               else failEC (resImp, Map.empty) . mkErrorFromInfo $
                 case mPre' of
                    Nothing -> UnresolvedName "type" (prettyPrint tn)
                    Just pre -> UnresolvedName "subpackage or type"
                                  (prettyPrint pre ++ "." ++ prettyPrint i)


      TypeImportOnDemand pos (Name pos' nt mPre i)
          | nt `elem` [POrTName, PName] -> do
              -- We ignore the PorT ambiguity and resolve this import as if
              -- the name has to be a package, i.e. we're importing a whole
              -- package, not the inner types of a type
              -- This is, of course, only correct because we don't support
              -- inner types
              mPre' <- resolvePre mPre

              let resName = Name pos' PName mPre' i
                  resImp  = TypeImportOnDemand pos resName

              -- Resolve as package or fail
              withPackage resName
                (do
                   piTypeIdents <- getPkgContents resName
                   let resExpn = expansionUnion $
                         map (mkTExpansionWithPrefix (Just resName)) piTypeIdents
                   return (resImp, resExpn))

      TypeImportOnDemand pos (Name pos' TName mPre i) -> do
              -- That name is a TName means this is an import statement for
              -- the inner classes of i
              mPre' <- resolvePre mPre
              let resName = Name pos' TName mPre' i
                  resImp  = TypeImportOnDemand pos resName

              withType resName
                (do -- resolve as type
                  _ast <- getTypeContents resName
                  -- TODO: Complete implementation: We don't actually support inner types yet
                  let resExpn = Map.empty
                  failEC (resImp, resExpn) $ mkError
                    (UnsupportedFeature $ "Inner types not supported: "
                                          ++ prettyPrint imp)
                    pos)

      _ -> do failEC (imp, Map.empty) $ mkErrorFromInfo
                (UnsupportedFeature $ "Static imports not yet supported: "
                                          ++ prettyPrint imp)


-- | Resolve prefix of a name
-- Always resolve as package name for now
resolvePre :: Maybe (Name SourcePos) -> PiReader (Maybe (Name SourcePos))
resolvePre Nothing = return Nothing
resolvePre (Just (Name pos nt mPre i))
    | nt `elem` [PName, POrTName] = do
                         mPre' <- resolvePre mPre
                         return $ Just (Name pos PName mPre' i)
resolvePre n = panic (nameResModule ++ ".resolvePre")
                   $ "Unexpected name: " ++ show n


-- | Execute action if given name is a package. Fails with error otherwise
withPackage :: MonadPR m => Name SourcePos -> m a -> m a
withPackage pkg@(Name pos _ _ _) action = do
  isP <- doesPkgExist pkg
  if isP then action
    else failE $
           mkError (UnresolvedName "package" (prettyPrint pkg)) pos


-- | Execute action if given name is a type. Compare to current name first
-- (I.e. to be called only in a context were the current name is a type)
-- Fails with error if argument not a type
withTypeCurr :: Name SourcePos -> NameRes a -> NameRes a
withTypeCurr typ@(Name pos _ _ _) action = do
  isT <- checkForType typ
  if isT then action
    else failE $
           mkError (UnresolvedName "type" (prettyPrint typ)) pos

-- | Execute action if given name is a type
-- Fails with error if argument not a type
withType :: MonadPR m => Name SourcePos -> m a -> m a
withType typ@(Name pos _ _ _) action = do
  isT <- doesTypeExist typ
  if isT then action
    else failE $
           mkError (UnresolvedName "type" (prettyPrint typ)) pos

-- | See if type of given name is in scope, by looking at pi-path and
-- comparing to the name of the type that we're currently resolving
checkForType :: Name SourcePos -> NameRes Bool
checkForType n = do
  n' <- getCurrentName
  -- debugPrint $ "checkForType: " ++ show (n, n')
  if n == n' then return True else doesTypeExist n

-- | A record for collecting various types of idents that need to be expanded
data ExpansionRecord = ExpansionRecord {
  expandTypes   :: [Ident SourcePos],
  expandMethods :: [Ident SourcePos],
  expandLocks   :: [Ident SourcePos],
  expandExps    :: [Ident SourcePos]
}

-- | Empty expansion record
newER :: ExpansionRecord
newER = ExpansionRecord [] [] [] []

-- | Perform expansion of all the idents in the expansion record
expandAll :: ExpansionRecord -> Expansion
expandAll (ExpansionRecord typs mthds lcks exprs) = expansionUnion $
                  map (mkEExpansion . unIdent) exprs ++
                  map (mkLExpansion . unIdent) lcks ++
                  map (mkMExpansion . unIdent) mthds ++
                  map (mkTExpansion . unIdent) typs
