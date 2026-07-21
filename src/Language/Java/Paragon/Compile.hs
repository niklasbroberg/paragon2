{-# LANGUAGE QuasiQuotes, PatternGuards #-}
module Language.Java.Paragon.Compile (compileTransform) where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Error()
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.Interaction

import Data.Generics.Uniplate.Data
import Data.List (nub, union, delete)
--import Data.Maybe (fromJust)
import Control.Arrow ((***))

import qualified Data.ByteString.Char8 as B

compilerModule :: String
compilerModule = libraryBase ++ ".Compile"

compileTransform :: CompilationUnit T -> CompilationUnit ()
compileTransform (CompilationUnit _ mp is tds) =
    -- Imports pass through untouched. A stale import of the flat v1
    -- `se.chalmers.paragon` package is a *source* error, rejected during name
    -- resolution (see NameResolution.buildMapFromImportName) rather than
    -- silently retargeted here at codegen.
    CompilationUnit () (fmap voidAnn mp) (map voidAnn is) $ map compileTypeDecl tds

compileTypeDecl :: TypeDecl T -> TypeDecl ()
compileTypeDecl td = 
    case td of
      ClassTypeDecl     _ cdecl -> ClassTypeDecl     () $ compileClassDecl     cdecl
      InterfaceTypeDecl _ idecl -> InterfaceTypeDecl () $ compileInterfaceDecl idecl


compileInterfaceDecl :: InterfaceDecl T -> InterfaceDecl ()
compileInterfaceDecl (InterfaceDecl _ ms i tps sups ibody) =
  let ms' = delete (Native ()) $ removeParagonMods ms -- No lockstate mods allowed here
                                                      -- In vanilla Java, native cannot appear on classes
      sups'  = map compileClassType_ sups
      (tps', _tpMembers, _tpPars, _tpAsss) = splitTypeParams tps
  in InterfaceDecl () ms' (voidAnn i) tps' sups' $
       compileInterfaceBody ibody

compileInterfaceBody :: InterfaceBody T -> InterfaceBody ()
compileInterfaceBody (InterfaceBody _ mds) = 
    InterfaceBody () $ map (compileSimpleMemberDecl [] []) mds

-- 1. Remove Paragon modifiers
-- 2. Transform Paragon type params into ordinary params
-- 3. Transform body
compileClassDecl :: ClassDecl T -> ClassDecl ()
compileClassDecl (ClassDecl _ ms i tps mSuper impls cbody) =
  let ms' = delete (Native ()) $ removeParagonMods ms -- No lockstate mods allowed here
                                                      -- In vanilla Java, native cannot appear on classes
      mSuper' = fmap compileClassType_ mSuper
      impls'  = map compileClassType_ impls
      (tps', tpMembers, tpPars, tpAsss) = splitTypeParams tps
  in ClassDecl () ms' (voidAnn i) tps' mSuper' impls' $
       compileClassBody cbody tpMembers tpPars tpAsss
compileClassDecl _ = panic (compilerModule ++ ".compileClassDecl")
                     $ "Enum not supported"

-- Paragon type parameters need to be replaced by runtime counterparts.
-- 1. Lock state parameters should be removed completed.
-- 2. Actor and Policy parameters need to be around at runtime. Each
--    parameter is translated into:
--     a) a field of the parameterized class
--     b) a parameter to every constructor of the class
--     c) an assignment of the parameter b) to the field a)
--        at the beginning of every constructor of the class
splitTypeParams :: [TypeParam T] 
                -> ([TypeParam ()],[MemberDecl ()],[FormalParam ()],[BlockStmt ()])
splitTypeParams = go ([],[],[],[]) -- error "compileTypeParams undefined"
    where 
      go (ttps,fds,fps,as) [] = (reverse ttps, reverse fds, reverse fps, reverse as)
      go (ttps,fds,fps,as) (tp:tps) = 
          case tp of
            TypeParam{}      -> go (voidAnn tp:ttps,fds,fps,as) tps -- Retain
            LockStateParam{} -> go (           ttps,fds,fps,as) tps -- Ignore
            _ -> let (i,ty) = 
                         case tp of
                           ActorParam  _ rt iP -> 
                               (voidAnn iP, -- [typeQQ| se.chalmers.paragon.ConcreteActor |]
                                RefType () (voidAnn rt))    -- concreteActorType)

                           PolicyParam _ iP -> 
                               (voidAnn iP, -- [typeQQ| se.chalmers.paragon.Policy        |]
                                policyType)
                           _ -> panic (compilerModule ++ ".splitTypeParams")
                                $ show tp
                     fd = --   [fieldDeclQQ| public final #T#ty #i; |]
                          FieldDecl () [Public (),Final ()] ty [VarDecl () (VarId () i) Nothing]
                     fp = -- [formalParamQQ| final #T#ty #i         |]
                          FormalParam () [Final ()] ty False (VarId () i)
                     a  = -- [blockStmtQQ| this.#i = #i;         |]
                          BlockStmt () (ExpStmt () (Assign () 
                             (FieldLhs () (PrimaryFieldAccess () (This ()) i)) 
                             (EqualA ()) (ExpName () (Name () EOrLName Nothing i))))
                 in go (ttps,fd:fds,fp:fps,a:as) tps

                                
compileClassBody :: ClassBody T -> [MemberDecl ()] -> [FormalParam ()] -> [BlockStmt ()] -> ClassBody ()
compileClassBody (ClassBody _ ds) tpMembers tpPars tpAsss = 
  let ds' = concat $ map (compileDecl tpPars tpAsss) ds
  in ClassBody () (map (MemberDecl ()) tpMembers ++ ds')

compileDecl :: [FormalParam ()] -> [BlockStmt ()] -> Decl T -> [Decl ()]
compileDecl _ _ (InitDecl _ _ _) = panic (compilerModule ++ ".compileDecl")
                                   $ "InitDecl not yet supported"
compileDecl tpPars tpAsss (MemberDecl _ md) = compileMemberDecl tpPars tpAsss md

compileMemberDecl :: [FormalParam ()] -> [BlockStmt ()] -> MemberDecl T -> [Decl ()]
compileMemberDecl tpPars tpAsss md =
    case md of
      LockDecl {} -> compileLockDecl md
      _ -> (:[]) . MemberDecl () $ compileSimpleMemberDecl tpPars tpAsss md

compileSimpleMemberDecl :: [FormalParam ()] -> [BlockStmt ()] -> MemberDecl T -> MemberDecl ()
compileSimpleMemberDecl tpPars tpAsss md =
    case md of
      -- Actors
      FieldDecl _ ms t vds -> compileVarDeclGeneric (FieldDecl ()) ms t vds

      MethodDecl _ ms tps rt i fps xs mb -> 
          let ms' = removeParagonMods ms
              (tps', _, tpPs, _) = splitTypeParams tps
              rt' = compileReturnType rt
              fps' = map compileFormalParam fps
              xs' = map compileExn xs
          in MethodDecl () ms' tps' rt' (voidAnn i) (tpPs ++ fps') xs' $ compileMethodBody mb

      ConstructorDecl _ ms tps i fps xs cb ->
          let ms' = removeParagonMods ms
              (tps', _, tpPs, _) = splitTypeParams tps
              fps' = map compileFormalParam fps
              xs'  = map compileExn xs
              -- Add the downgraded type parameters: class parameters (tpPars) first,
              -- then parameters specific to this constructor (tpPs)
          in ConstructorDecl () ms' tps' (voidAnn i) (tpPars ++ tpPs ++ fps') xs' 
                 $ compileConstrBody tpAsss cb

      _ -> panic (compilerModule ++ ".compileSimpleMemberDecl")
           $ prettyPrint md -- Locks should be filtered out already

compileConstrBody :: [BlockStmt ()] -> ConstructorBody T -> ConstructorBody ()
compileConstrBody tpAsss (ConstructorBody _ meci bss) = 
    -- Add the initialization of the downgraded type parameters
    ConstructorBody () (fmap compileECI meci) (tpAsss ++ map compileBlockStmt bss)

compileECI :: ExplConstrInv T -> ExplConstrInv ()
compileECI (ThisInvoke  _ tas as) = 
    let (trueTas, demotedArgs) = splitNWTypeArgs tas
    in ThisInvoke  () trueTas (demotedArgs ++ map compileExp as)
compileECI (SuperInvoke _ tas as) = 
    let (trueTas, demotedArgs) = splitNWTypeArgs tas
    in SuperInvoke () trueTas (demotedArgs ++ map compileExp as)
compileECI (PrimarySuperInvoke _ e tas as) = 
    let (trueTas, demotedArgs) = splitNWTypeArgs tas
    in PrimarySuperInvoke () (compileExp e) trueTas (demotedArgs ++ map compileExp as)

compileFormalParam :: FormalParam T -> FormalParam ()
compileFormalParam (FormalParam _ ms t va vid) = 
    FormalParam () (removeParagonMods ms) (compileType t) va (voidAnn vid)

actorVarDecl, policyVarDecl, compileVarDecl :: VarDecl T -> VarDecl ()
actorVarDecl (VarDecl _ (VarId _ i) Nothing)
    = -- v2: a fresh actor is just a fresh object.  `$$i = new Object()`
      vDecl (voidAnn i) newObject
actorVarDecl vd = compileVarDecl vd

policyVarDecl (VarDecl _ (VarId _ i)
                           (Just (InitExp _ (PolicyExp _ (PolicyLit _ cs)))))
    = -- v2 Policy has no name; it is just its clauses.  `$$i = new Policy(cs...)`
      vDecl (voidAnn i) $ newRT "Policy" (map clauseToExp cs)
policyVarDecl vd = compileVarDecl vd

compileVarDecl (VarDecl _ vid mInit) = VarDecl () (voidAnn vid) $ fmap compileVarInit mInit

compileExn :: ExceptionSpec T -> ExceptionSpec ()
compileExn (ExceptionSpec _ _ms rt) = ExceptionSpec () [] -- no modifiers on exceptions in java!
                                       $ compileRefType rt

compileReturnType :: ReturnType T -> ReturnType ()
compileReturnType (LockType _) = Type () $ PrimType () $ BooleanT ()
compileReturnType (Type _ t)   = Type () $ compileType t
compileReturnType rett = voidAnn rett

compileType :: Type T -> Type ()
compileType (RefType _ rt) = RefType () $ compileRefType rt
compileType t@(PrimType _ pt) = case pt of
                                  ActorT _  -> concreteActorType
                                  PolicyT _ -> policyType
                                  _ -> voidAnn t
compileType t = voidAnn t

compileRefType :: RefType T -> RefType ()
compileRefType (ArrayType _ t mps) = 
    ArrayType () (compileType t) $ map (const Nothing) mps -- No policy parameters!
compileRefType (ClassRefType _ ct) = ClassRefType () $ compileClassType_ ct
compileRefType rt = voidAnn rt

compileClassType :: ClassType T -> (ClassType (), [Argument ()])
compileClassType (ClassType _ n tas) = 
    let (trueTas, demotedArgs) = splitTypeArgs tas
    in (ClassType () (voidAnn n) trueTas, demotedArgs)

-- When we don't care about demoted policies and actors
compileClassType_ :: ClassType T -> ClassType ()
compileClassType_ = fst . compileClassType

--compileTypeArgs :: [TypeArgument T] -> [TypeArgument ()]
--compileTypeArgs _ = [] -- TODO: Cheating!!!

--compileNWTypeArgs :: [NonWildTypeArgument T] -> [NonWildTypeArgument ()]
--compileNWTypeArgs _ = [] -- TODO: Cheating!!!

compileMethodBody :: MethodBody T -> MethodBody ()
compileMethodBody (MethodBody _ (Just bl)) = MethodBody () . Just $ compileBlock bl
compileMethodBody mb = voidAnn mb

compileBlock :: Block T -> Block ()
compileBlock (Block _ bss) = Block () $ map compileBlockStmt bss

compileBlockStmt :: BlockStmt T -> BlockStmt ()
compileBlockStmt (BlockStmt _ stmt) = BlockStmt () $ compileStmt stmt
compileBlockStmt (LocalVars _ ms t vds) = compileVarDeclGeneric (LocalVars ()) ms t vds
compileBlockStmt bss = panic (compilerModule ++ ".compileBlockStmt")
                       $ prettyPrint bss

compileVarDeclGeneric :: ([Modifier ()] -> Type () -> [VarDecl ()] -> res)
                       -> [Modifier T ] -> Type T  -> [VarDecl T ] -> res
compileVarDeclGeneric con ms t vds =
    let (t', vds') = case t of
                       PrimType _ (PolicyT _) -> (policyType, map policyVarDecl vds)
--                       PrimType _ (ActorT  _) -> (concreteActorType, map actorVarDecl vds)
                       _ -> (compileType t, map compileVarDecl vds)
    in con (removeParagonMods ms)  t' vds'



compileStmt :: Stmt T -> Stmt ()
compileStmt (StmtBlock _ bl) = StmtBlock () $ compileBlock bl
-- v2 lock state is external and value-based:
--   LockState.open(new Lock(<lockID>, actors...))
compileStmt (Open _ (Lock _ lN aN)) = ExpStmt () $ callStatic "LockState" "open"
         [ newRT "Lock" (ExpName () (voidAnn lN) : map actorNameToArg aN) ]
compileStmt (Close _ (Lock _ lN aN)) = ExpStmt () $ callStatic "LockState" "close"
         [ newRT "Lock" (ExpName () (voidAnn lN) : map actorNameToArg aN) ]
compileStmt (OpenBlock  _ _ bl) = StmtBlock () $ compileBlock bl
compileStmt (CloseBlock _ _ bl) = StmtBlock () $ compileBlock bl

compileStmt (IfThen _ e s) = IfThen () (compileExp e) (compileStmt s)
compileStmt (IfThenElse _ e th el) = IfThenElse () (compileExp e) (compileStmt th) (compileStmt el)
compileStmt (While _ e s) = While () (compileExp e) (compileStmt s)
compileStmt (BasicFor _ mIn mTest mUp s) =
    let mIn' = fmap compileForInit mIn
        mTest' = fmap compileExp mTest
        mUp' = fmap (map compileExp) mUp
    in BasicFor () mIn' mTest' mUp' $ compileStmt s
compileStmt (ExpStmt _ e) = ExpStmt () $ compileExp e
compileStmt (Return _ me) = Return () $ fmap compileExp me
compileStmt (Throw _ e) = Throw () $ compileExp e
compileStmt (Try _ bl cs mfin) = Try () (compileBlock bl) (map compileCatch cs) (fmap compileBlock mfin)
compileStmt st = voidAnn st

compileForInit :: ForInit T -> ForInit ()
compileForInit (ForInitExps _ es) = ForInitExps () $ map compileExp es
compileForInit (ForLocalVars _ ms t vds) = compileVarDeclGeneric (ForLocalVars ()) ms t vds

compileCatch :: Catch T -> Catch ()
compileCatch (Catch _ fp bl) = Catch () (compileFormalParam fp) (compileBlock bl)

compileVarInit :: VarInit T -> VarInit ()
compileVarInit (InitExp   _ e ) = InitExp   () $ compileExp e
compileVarInit (InitArray _ ai) = InitArray () $ compileArrayInit ai

compileArrayInit :: ArrayInit T -> ArrayInit ()
compileArrayInit (ArrayInit _ vis) = ArrayInit () $ map compileVarInit vis

--compileExp :: Exp T -> Exp ()
--compileExp = transformBi compileExp'

-- TODO: Fill out full, since no longer generic
compileExp :: Exp T -> Exp ()
compileExp (PolicyExp _ pe) = compilePolicyExp pe

-- For instance creation, we need to move type
-- arguments to actual arguments -- but not right now!
compileExp (InstanceCreation a tas ct args mcbody) = 
    let isNative = maybe False snd a
        (trueTas, demotedArgs) = splitTypeArgs tas
        (ct', classDemotedArgs) = compileClassType ct
        extraArgs = if isNative then [] else demotedArgs ++ classDemotedArgs
    -- Here we need to demote the args in the ct as well!!!
    in InstanceCreation () trueTas ct' (extraArgs ++ map compileExp args)
                         (fmap (\cb -> compileClassBody cb [] [] []) mcbody)
{-
compileExp (QualInstanceCreation e tas i args mcbody) = do
  undefined -}
compileExp (ArrayCreate _ t edims idims) =
    let edims' = map (compileExp *** const Nothing) edims
        idims' = map (const Nothing) idims
    in ArrayCreate () (compileType t) edims' idims'
compileExp e@(ArrayCreateInit{}) = 
    error $ "Compilation of ArrayCreateInit not yet supported: " ++ prettyPrint e

compileExp (FieldAccess _ fa) = FieldAccess () $ compileFieldAccess fa
compileExp (MethodInv _ mi) = MethodInv () $ compileMethodInv mi
compileExp (ArrayAccess _ ai) = ArrayAccess () $ compileArrayIndex ai

compileExp (PostIncrement _ e) =  PostIncrement () $ compileExp e
compileExp (PreIncrement  _ e) =  PreIncrement  () $ compileExp e
compileExp (PostDecrement _ e) =  PostDecrement () $ compileExp e
compileExp (PreDecrement  _ e) =  PreDecrement  () $ compileExp e

compileExp (PrePlus     _ e) =  PrePlus     () $ compileExp e
compileExp (PreMinus    _ e) =  PreMinus    () $ compileExp e
compileExp (PreBitCompl _ e) =  PreBitCompl () $ compileExp e
compileExp (PreNot      _ e) =  PreNot      () $ compileExp e

compileExp (Cast _ t e) = Cast () (compileType t) (compileExp e)

-- Lock names must be handled in a special way - but not right now!
compileExp (ExpName _ n) = ExpName () $ voidAnn n
compileExp (LockExp _ l) = lockExpToExp l

-- Certain operators have special effects on paragon types
compileExp (BinOp _ e1 op e2) = compileBinOp (voidAnn op) e1 e2

compileExp (ClassLit _ mt) = ClassLit () (fmap compileType mt)
compileExp (Paren _ e) = Paren () $ compileExp e
compileExp (Cond _ c th el) = Cond () (compileExp c) (compileExp th) (compileExp el)

compileExp (Assign _ lhs aop e) = compileAOp (voidAnn aop) lhs e 
--    Assign () (compileLhs lhs) (compileAOp aop) (compileExp e)

compileExp e@(InstanceOf{}) = 
    error $ "Compilation of InstanceOf not yet supported: " ++ prettyPrint e

-- Lit, This, ThisClass, AntiQExp
compileExp e = voidAnn e


compileMethodInv :: MethodInvocation T -> MethodInvocation ()
compileMethodInv mi = case mi of
  MethodCallOrLockQuery _ n@(Name _ LName _ _) as ->
      -- Lock query `L(a...)` -> LockState.isOpen(new Lock(L, new Actor(a)...))
      MethodCallOrLockQuery ()
         (Name () MName (Just $ mkPkgTypeName "LockState") (Ident () (B.pack "isOpen")))
         [ newRT "Lock" (ExpName () (voidAnn n) : map (wrapActor . compileExp) as) ]

  MethodCallOrLockQuery _ n as -> MethodCallOrLockQuery () (voidAnn n) $ map compileExp as
  PrimaryMethodCall _ e tas i as -> 
      let isNative = maybe False snd $ ann mi
          (trueTas,demotedArgs) = splitNWTypeArgs tas
          args = (if isNative then id else (demotedArgs ++)) $ map compileExp as
       in PrimaryMethodCall () (compileExp e) trueTas (voidAnn i) args
  TypeMethodCall _ n tas i as ->
      let isNative = maybe False snd $ ann mi
          (trueTas,demotedArgs) = splitNWTypeArgs tas
          args = (if isNative then id else (demotedArgs ++)) $ map compileExp as
       in TypeMethodCall () (voidAnn n) trueTas (voidAnn i) args
  _ -> panic (compilerModule ++ ".compileMethodInv")
       $ prettyPrint mi

splitTypeArgs :: [TypeArgument T] -> ([TypeArgument ()], [Argument ()])
splitTypeArgs = go ([], [])
    where
      go (ttas, as) [] = (reverse ttas, reverse as)
      go (ttas, as) (ta:tas) =
          case ta of
            Wildcard{} -> panic (compilerModule ++ ".splitTypeArgs") $
                          "Wildcards not yet supported"
                          -- go (compileWildcard ta:ttas, as) tas
            ActualArg _ nwta ->
                case nwta of
                  ActualType _ rt -> 
                      let ta' = ActualArg () $ ActualType () $ compileRefType rt
                      in go (ta':ttas, as) tas
                  ActualName _ (Name _ TName _ _) -> go (voidAnn ta:ttas, as) tas
                  ActualName _ n@(Name _ EName _ _) -> go (ttas, ExpName () (voidAnn n) : as) tas
                  ActualExp _ e -> go (ttas, compileExp e : as) tas
                  -- Lock states and lock names have no runtime counterpart, so we just ignore those
                  _ -> go (ttas, as) tas

splitNWTypeArgs :: [NonWildTypeArgument T] -> ([NonWildTypeArgument ()], [Argument ()])
splitNWTypeArgs = go ([], [])
    where
      go (ttas, as) [] = (reverse ttas, reverse as)
      go (ttas, as) (nwta:tas) =
                case nwta of
                  ActualType{} -> go (voidAnn nwta:ttas, as) tas
                  ActualName _ (Name _ TName _ _) -> go (voidAnn nwta:ttas, as) tas
                  ActualName _ n@(Name _ EName _ _) -> go (ttas, ExpName () (voidAnn n) : as) tas
                  ActualExp _ e -> go (ttas, compileExp e : as) tas
                  -- Lock states and lock names have no runtime counterpart, so we just ignore those
                  _ -> go (ttas, as) tas

-- Compiling binary operators. The interesting cases are
-- the ones where the operands are policies.
compileBinOp :: Op () -> Exp T -> Exp T -> Exp ()
compileBinOp op e1 e2
             | Just (t1, _) <- ann e1, t1 == policyT,
               Just (t2, _) <- ann e2, t2 == policyT,
               op `elem` [Mult (), Add ()] = 
                   mkParagonPolicyOp op (compileExp e1) (compileExp e2)
compileBinOp op e1 e2 = BinOp () (compileExp e1) op (compileExp e2)

mkParagonPolicyOp :: Op () -> Exp () -> Exp () -> Exp ()
mkParagonPolicyOp op e1 e2 =
    case op of
      Mult _ -> MethodInv () $
                 PrimaryMethodCall () e1 [] (Ident () (B.pack "join")) [e2]
      Add  _ -> MethodInv () $
                 PrimaryMethodCall () e1 [] (Ident () (B.pack "meet")) [e2]
      _ -> panic (compilerModule ++ ".mkParagonPolicyOp")
           $ "Unexpected operator: " ++ show op
                  
mkParagonPolicyAssign :: AssignOp () -> Lhs () -> Exp () -> Exp ()
mkParagonPolicyAssign aop lhs e = 
    case aop of
      MultA _ -> MethodInv () $
                  PrimaryMethodCall () (lhsToExp lhs) []
                   (Ident () (B.pack "joinWith")) [e]
      AddA  _ -> MethodInv () $
                  PrimaryMethodCall () (lhsToExp lhs) []
                   (Ident () (B.pack "meetWith")) [e]
      _ -> Assign () lhs aop e

lhsToExp :: Lhs () -> Exp ()
lhsToExp (NameLhs _ n) = ExpName () n
lhsToExp (FieldLhs _ fa) = FieldAccess () fa
lhsToExp (ArrayLhs _ ai) = ArrayAccess () ai

-- A lock used as a boolean: LockState.isOpen(new Lock(<lockID>, actors...))
lockExpToExp :: Lock T -> Exp ()
lockExpToExp (Lock _ n ans) =
  callStatic "LockState" "isOpen"
    [ newRT "Lock" (ExpName () (voidAnn n) : map actorNameToArg ans) ]
lockExpToExp (LockVar _ i) =
  callStatic "LockState" "isOpen"
    [ ExpName () (mkSimpleName EName $ voidAnn i) ]

-----
compileLhs :: Lhs T -> Lhs ()
compileLhs lhs =
    case lhs of
      NameLhs _ n -> NameLhs () (voidAnn n)
      ArrayLhs _ ai -> ArrayLhs () $ compileArrayIndex ai
      FieldLhs _ fa -> FieldLhs () $ compileFieldAccess fa

compileAOp :: AssignOp () -> Lhs T -> Exp T -> Exp ()
compileAOp aop lhs e
    | Just (t1,_) <- ann lhs, t1 == policyT,
      Just (t2,_) <- ann e,   t2 == policyT,
      aop `elem` [MultA (), AddA ()] = 
          mkParagonPolicyAssign aop (compileLhs lhs) (compileExp e)
compileAOp aop lhs e = Assign () (compileLhs lhs) aop (compileExp e)      

compileArrayIndex :: ArrayIndex T -> ArrayIndex ()
compileArrayIndex (ArrayIndex _ eArr eI) 
    = ArrayIndex () (compileExp eArr) (compileExp eI)

compileFieldAccess :: FieldAccess T -> FieldAccess ()
compileFieldAccess fa =
    case fa of
      PrimaryFieldAccess _ e i -> 
          PrimaryFieldAccess () (compileExp e) (voidAnn i)
      _ -> voidAnn fa

--------------------------------------------
-- Compiling lock and policy declarations

-- Policies

compilePolicyExp :: PolicyExp T -> Exp ()
compilePolicyExp (PolicyLit _ cs) = newRT "Policy" (map clauseToExp cs)
compilePolicyExp (PolicyTypeVar _ i) = ExpName () (mkSimpleName EName $ voidAnn i)
-- PolicyOf may only appear in modifiers, which will have been removed.
compilePolicyExp pe =
    panic (compilerModule ++ ".compilePolicyExp") 
              $ prettyPrint pe


-- Clauses and components

clauseToExp :: Clause T -> Exp ()
clauseToExp (Clause _ cvds h body) =
    let -- Types of the quantified variables, keyed by name.  The head may also
        -- declare one (ClauseDeclHead).  v2's Clause is type-aware: the sets
        -- array types each `new Variable(k)` occurring below.
        headDecls = case h of
                      ClauseDeclHead _ cvd -> [cvd]
                      _                    -> []
        varTypes = [ (voidAnn i, compileRefType rt)
                   | ClauseVarDecl _ rt i <- headDecls ++ cvds ]
        vs = nub [ a | Var _ a <- universeBi (clauseHeadToActor $ voidAnn h)
                               ++ universeBi (map voidAnn body) ]
             `zip` [0..] -- Substs
        sets = [ maybe objectRefType id (lookup ident varTypes) | (ident, _) <- vs ]
        exps = clauseHeadToExp vs h : map (atomToExp vs) body
     in newRT "Clause" (setsArray sets : exps)

clauseHeadToActor :: ClauseHead () -> Actor ()
clauseHeadToActor (ClauseDeclHead _ (ClauseVarDecl _ _ i)) = Var () i
clauseHeadToActor (ClauseVarHead _ a) = a

clauseHeadToExp :: [(Ident (), Int)] -> ClauseHead T -> Exp ()
clauseHeadToExp vs (ClauseDeclHead _ (ClauseVarDecl t _ i)) =
    actorToExp vs (Var Nothing i)
clauseHeadToExp vs (ClauseVarHead _ a) = actorToExp vs a

-- An atom is a lock predicate: `new Atom(<lockID>, args...)`.  The lock name
-- resolves to the static final LockID field emitted by compileLockDecl.  (v2
-- has no ActorList; a clause head is a bare Argument, a lock-property head is
-- itself an Atom, so both go through atomToExp / actorToExp directly.)
atomToExp :: [(Ident (), Int)] -> Atom T -> Exp ()
atomToExp vs (Atom _ n acts) =
    newRT "Atom" (ExpName () (voidAnn n) : map (actorToExp vs) acts)

-- Compile an actor position to a runtime Argument: a concrete actor becomes
-- `new Actor(obj)`, a quantified variable becomes `new Variable(k)`.
actorToExp :: [(Ident (), Int)] -> Actor T -> Exp ()
actorToExp _vs (Actor _ (ActorName _ n)) = wrapActor $ ExpName () (voidAnn n)
actorToExp _vs (Actor _ (ActorTypeVar _ _rt tv)) = wrapActor $ ExpName () (mkSimpleName EName (voidAnn tv))
actorToExp vs (Var _ i) =
    let res = lookup (voidAnn i) vs
        k = case res of
              Just m -> fromIntegral m
              Nothing -> panic (compilerModule ++ ".actorToExp")
                         $ "No such actor variable: " ++ show (i, vs)
     in newRT "Variable" [Lit () $ Int () k]


-- Locks

-- Compile a lock declaration into a (static) Lock declaration 
-- plus (static) initialization of its lock properties.
-- Precondition: md is a LockDecl
compileLockDecl :: MemberDecl T -> [Decl ()]
compileLockDecl md =
    case md of
      LockDecl _ ms i@(Ident _ rawI) pars mLProps ->
              let -- Properties defined in modifiers
                  lmExps = map (lockModToExp i) $ filter isLockMod ms
                  -- Properties defined explicitly
                  lpExps = maybe [] 
                             (map (lockPropToExp i) . (\(LockProperties _ cs) -> cs)) 
                             mLProps
                  -- v2 LockID is type-aware: the arity is the actual parameter
                  -- classes, not just a count.  `new LockID("L", T0.class, ...)`
                  arity = [ ClassLit () (Just (RefType () (compileRefType par))) | par <- pars ]
                  lockE = newRT "LockID" (Lit () (String () $ B.unpack rawI) : arity)
                  lockD = FieldDecl () ([Static (),Final ()] `union` removeParagonMods ms)
                            lockIDType
                            [vDecl (voidAnn i) lockE]
              in MemberDecl () lockD : 
                        lockExpsToInit i (lmExps ++ lpExps)

      _ -> fail $ "Internal error: compileLockDecl: " ++ show md


-- Initialization code for lock properties
lockExpsToInit :: Ident T -> [Exp ()] -> [Decl ()]
lockExpsToInit _ [] = []
lockExpsToInit _i es = [InitDecl () True . Block () $
                        map (BlockStmt () . ExpStmt ()) es]
                        
-- v2 lock properties are global and value-based: a LockProperty (typed head
-- Atom + body Atoms, with a sets array) registered on GlobalPolicy, rather than
-- a clause mutated onto the lock instance.
lockPropToExp :: Ident T -> LClause T -> Exp ()
lockPropToExp _i (LClause _ cvds h body) =
    let varTypes = [ (voidAnn vi, compileRefType rt) | ClauseVarDecl _ rt vi <- cvds ]
        vs = nub [ a | Var _ a <- universeBi (map voidAnn (h:body)) ] `zip` [0..] -- Substs
        sets = [ maybe objectRefType id (lookup ident varTypes) | (ident, _) <- vs ]
        prop = newRT "LockProperty"
                 (setsArray sets : atomToExp vs h : map (atomToExp vs) body)
    in callStatic "GlobalPolicy" "addProperty" [prop]
lockPropToExp i _ = panic (compilerModule ++ ".lockPropToExp")
                    $ prettyPrint i

lockModToExp :: Ident T -> Modifier T -> Exp ()
lockModToExp (Ident _ rawI) m = 
    let mname = prettyPrint m
     in call [B.unpack rawI,mname] []
lockModToExp i _ = panic (compilerModule ++ ".lockModToExp")
                   $ prettyPrint i


isLockMod :: Modifier a -> Bool
isLockMod m = case m of
  Reflexive  _ -> True
  Transitive _ -> True
  Symmetric  _ -> True
  _ -> False               

isParagonMod :: Modifier a -> Bool
isParagonMod m = case m of
  Typemethod _ -> True
  Readonly   _ -> True
  Notnull    _ -> True
  Reflexive  _ -> True
  Transitive _ -> True
  Symmetric  _ -> True
  Reads _    _ -> True
  Writes _   _ -> True
  Opens _    _ -> True
  Closes _   _ -> True
  Expects _  _ -> True
  _ -> False

removeParagonMods :: [Modifier a] -> [Modifier ()]
removeParagonMods = map voidAnn . filter (not . isParagonMod) 

callStatic :: String -> String -> [Exp ()] -> Exp ()
callStatic typ met args = 
    MethodInv () $ MethodCallOrLockQuery () 
                  (Name () MName (Just $ mkPkgTypeName typ) (Ident () (B.pack met))) args

call :: [String] -> [Exp ()] -> Exp ()
call strs args = 
    MethodInv () $ MethodCallOrLockQuery () (mkName const MName EName $ map (Ident () . B.pack) strs) args

vDecl :: Ident () -> Exp () -> VarDecl ()
vDecl i initz = VarDecl () (VarId () i) (Just $ InitExp () initz)


pkgPrefix :: Name ()
pkgPrefix = mkUniformName const PName $ map (Ident () . B.pack) ["se","chalmers","paragon","runtime"]

mkPkgTypeName :: String -> Name ()
mkPkgTypeName str = Name () TName (Just pkgPrefix) (Ident () (B.pack str))

mkPkgType :: String -> Type ()
mkPkgType str = RefType () $ ClassRefType () $ ClassType () (mkPkgTypeName str) []

-- The v2 runtime is value/constructor-based rather than static-factory-based:
-- e.g. `new Policy(clauses...)`, `new Clause(sets, head, body...)`,
-- `new Actor(obj)`, `new Variable(k)`, `new Lock(lockID, actors...)`. These
-- helpers emit `new se.chalmers.paragon.runtime.<T>(args)` and `new <T>(args)`.
newRT :: String -> [Exp ()] -> Exp ()
newRT typ args =
    InstanceCreation () [] (ClassType () (mkPkgTypeName typ) []) args Nothing

newPlain :: String -> [Exp ()] -> Exp ()
newPlain typ args =
    InstanceCreation () [] (ClassType () (Name () TName Nothing (Ident () (B.pack typ))) []) args Nothing

-- v2 makes actors plain objects; the object *is* the identity.
newObject :: Exp ()
newObject = newPlain "Object" []

-- Wrap an actor object expression as a runtime Argument: `new Actor(e)`.
wrapActor :: Exp () -> Exp ()
wrapActor e = newRT "Actor" [e]

-- An actor named at a lock open/close/query site, wrapped as `new Actor(...)`
-- for the `Lock(LockID, Actor...)` constructor.
actorNameToArg :: ActorName T -> Exp ()
actorNameToArg (ActorName _ n)      = wrapActor $ ExpName () (voidAnn n)
actorNameToArg (ActorTypeVar _ _ i) = wrapActor $ ExpName () (mkSimpleName EName (voidAnn i))

objectRefType :: RefType ()
objectRefType = ClassRefType () (ClassType () (Name () TName Nothing (Ident () (B.pack "Object"))) [])

objectType :: Type ()
objectType = RefType () objectRefType

-- The element type `Class<?>` for the `Class<?>[] sets` arrays that v2's
-- type-aware Clause/LockProperty constructors expect.
classWildType :: Type ()
classWildType = RefType () $ ClassRefType () $
    ClassType () (Name () TName Nothing (Ident () (B.pack "Class"))) [Wildcard () Nothing]

-- `new Class<?>[]{ T0.class, T1.class, ... }` — one class literal per clause
-- variable, indexed to match the `new Variable(k)` it types.
setsArray :: [RefType ()] -> Exp ()
setsArray rts =
    ArrayCreateInit () classWildType [Nothing] $
      ArrayInit () [ InitExp () (ClassLit () (Just (RefType () rt))) | rt <- rts ]

concreteActorType, policyType, lockType, lockIDType :: Type ()
concreteActorType = objectType          -- v2: a Paragon actor is a plain Object
policyType        = mkPkgType "Policy"
lockType          = mkPkgType "Lock"
lockIDType        = mkPkgType "LockID"   -- a lock *declaration* is its LockID

voidAnn :: Annotated ast => ast a -> ast ()
voidAnn = fmap (const ())
